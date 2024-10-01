#include "llvm/Transforms/RGM/rgm.h"
#include "CFMelder/BranchFusion.h"
#include "CFMelder/PtrToRefUtils.h"
#include "CFMelder/RegionMelder.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/CGSCCPassManager.h"
#include "llvm/Analysis/DivergenceAnalysis.h"
#include "llvm/Analysis/DominanceFrontier.h"
#include "llvm/Analysis/DominanceFrontierImpl.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/Analysis/RegionInfoImpl.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar/Reg2Mem.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/Mem2Reg.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"
#include <fstream>
#include <llvm/IR/BasicBlock.h>
#include <llvm/Support/Casting.h>
#include <unordered_map>
#include <unordered_set>
using namespace llvm;

#define Debug true
#define EnableSALSSACoalescing true
#define ENABLE_TIMING

#define MATCH_NUM 20
#define MATCH_RATIO 0.3
#define SCORE_THRESHOLD 0.4

#define DEBUG_TYPE "rgm"
STATISTIC(regionNotExistNum, "The # of not exist regions");
STATISTIC(adjacentRegionNum, "The # of adjacent regions");
STATISTIC(mergeGenFailNum, "The # of error during merge gen regions");
STATISTIC(ProcessPHIsErrorNum, "The # of error during processing PHIs");
STATISTIC(notProfitableLocalNum,
          "The # of locally not profitable region pairs");
STATISTIC(commitChangesErrorNum, "The # of error during commiting change");
STATISTIC(matchedRegionPairsNum, "The # of matched region pairs");
STATISTIC(mergeRegionPairsNum, "The # of merge region pairs");
STATISTIC(notProfitableGlobalNum,
          "The # of globally not profitable region pairs");
STATISTIC(runRegionMatchTime,
          "Time spent in collecting leaf region in microseconds");
STATISTIC(findSimilarRegionTime, "Time spent in collecting isomorphic region "
                                 "and calculating score in microseconds");
STATISTIC(candidatesRankingTime,
          "Time spent in candidate ranking in microseconds");
STATISTIC(regionMergingTime, "Time spent in region merging in microseconds");
STATISTIC(alignBlocksTime, "Time spent in sequence alignment in microseconds");
STATISTIC(mergeGenTime, "Time spent in merging locally in microseconds");
STATISTIC(getRegionTime, "Time spent in getting region in microseconds");
STATISTIC(resumeCodeTime, "Time spent in resuming code in microseconds");
STATISTIC(allTime, "Time spent totally in microseconds");
STATISTIC(regionSize, "The region size");
STATISTIC(hasBranchFusion, "Check has branch fusion");

static cl::opt<double> scoreThreshold("rgm-score-threshold", cl::init(0.35),
                                      cl::Hidden,
                                      cl::desc("rgm-score-threshold"));

static cl::opt<double> matchRatio("rgm-match-ratio", cl::init(0.55), cl::Hidden,
                                  cl::desc("rgm-match-ratio"));

static cl::opt<int> regionSizeThreshold("rgm-rgs-threshold", cl::init(15),
                                        cl::Hidden,
                                        cl::desc("rgm-rgs-threshold"));

static cl::opt<int> matchThreshold("rgm-match-threshold", cl::init(20),
                                   cl::Hidden, cl::desc("rgm-match-threshold"));

static cl::opt<double> matchArg("rgm-match-arg", cl::init(0.3), cl::Hidden,
                                cl::desc("rgm-match-arg"));

// static cl::opt<bool> enableBfcase("rgm-enable-bfcase", cl::init(true),
//                                   cl::Hidden, cl::desc("rgm-enable-bfcase"));

class SESERegion {
public:
  BasicBlock *Entry;
  std::vector<BasicBlock *> Blocks;
  std::vector<BasicBlock *> Exits;

public:
  using iterator =
      PtrToRefIterator<BasicBlock, std::vector<BasicBlock *>::iterator>;

  SESERegion(Region *R) : Entry(R->getEntry()) {
    for (auto it : R->blocks()) {
      Blocks.push_back(it);
    }
    Exits.push_back(R->getExit());
  }

  const BasicBlock &getEntryBlock() const { return *Entry; }
  BasicBlock &getEntryBlock() { return *Entry; }

  bool contains(BasicBlock *BB) {
    return std::find(Blocks.begin(), Blocks.end(), BB) != Blocks.end();
  }
  bool isExitBlock(BasicBlock *BB) {
    return std::find(Exits.begin(), Exits.end(), BB) != Exits.end();
  }

  iterator begin() { return iterator(Blocks.begin()); }
  iterator end() { return iterator(Blocks.end()); }

  iterator exit_begin() { return iterator(Exits.begin()); }
  iterator exit_end() { return iterator(Exits.end()); }

  iterator_range<iterator> exits() {
    return make_range<iterator>(exit_begin(), exit_end());
  }

  size_t size() { return Blocks.size(); }

  size_t getNumExitBlocks() { return Exits.size(); }

  BasicBlock *getUniqueExitBlock() {
    if (Exits.size() == 1)
      return *Exits.begin();
    else
      return nullptr;
  }
};

class RegionTree {
private:
  Region *region;
  RegionTree *parent;
  std::vector<RegionTree *> child;
  std::vector<BasicBlock *> blocks;

public:
  int matchId;
  int level;
  BasicBlock *EntryBlock;
  BasicBlock *ExitBlock;

  RegionTree(Region *region) : region(region), matchId(-1), level(0) {
    for (auto it : region->blocks()) {
      blocks.push_back(it);
    }
    if (auto r = region->getExit()) {
      blocks.push_back(r);
    }
    EntryBlock = region->getEntry();
    ExitBlock = region->getExit();
  }

  Region *getRegion() { return region; }

  RegionTree *getParent() { return parent; }

  void setParent(RegionTree *parent) { this->parent = parent; }

  std::vector<RegionTree *> getChild() { return child; }

  void setChild(std::vector<RegionTree *> child) { this->child = child; }

  std::vector<BasicBlock *> getBlocks() { return blocks; }
};

class Match {
public:
  std::pair<RegionTree *, RegionTree *> match;
  double similarityScores;
  int level;
};

static bool simplifyFunction(Function &F, TargetTransformInfo &TTI,
                             SimplifyCFGOptions &Options) {
  bool Changed = false;
  bool LocalChange = false;
  do {
    LocalChange = false;
    for (auto &BB : make_range(F.begin(), F.end())) {
      if (simplifyCFG(&BB, TTI, nullptr, Options)) {
        LocalChange = true;
        break;
      }
    }

    Changed |= LocalChange;

  } while (LocalChange);
  return Changed;
}

static int readCounter(const std::string &filename) {
  std::ifstream infile(filename);
  int counter = 0;
  if (infile.is_open()) {
    infile >> counter;
    infile.close();
  }
  return counter;
}

static void writeCounter(const std::string &filename, int counter) {
  std::ofstream outfile(filename);
  if (outfile.is_open()) {
    outfile << counter;
    outfile.close();
  }
}

static bool runRegionMatch(Function &F, DominatorTree &DT,
                           PostDominatorTree &PDT, LoopInfo &LI,
                           TargetTransformInfo &TTI,
                           std::vector<RegionTree *> &regions) {
  // errs() << "Function name : " << F.getName() << "\n";
  ControlFlowGraphInfo *CFGInfo = new ControlFlowGraphInfo(F, DT, PDT, TTI);
  auto RI = CFGInfo->getRegionInfo();
  Region *region = RI->getTopLevelRegion();
  region->dump();
  errs() << "==============\n";
  SmallVector<RegionTree *, 32> WorkList;
  RegionTree *RT = new RegionTree(RI->getTopLevelRegion());
  WorkList.push_back(RT);
  while (!WorkList.empty()) {
    RegionTree *parent = WorkList.pop_back_val();
    Region *R = parent->getRegion();
    if (R->begin() == R->end()) {
      // if (R->isSimple())
      regions.push_back(parent);
      continue;
    }
    std::vector<RegionTree *> childArr;
    for (auto &SubR : *R) {
      RegionTree *child = new RegionTree(SubR.get());
      child->setParent(parent);
      WorkList.push_back(child);
      childArr.push_back(child);
    }
    parent->setChild(childArr);
  }

  return false;
}

static int Find(std::vector<int> &group, int v) {
  if (group[v] == v)
    return v;
  return group[v] = Find(group, group[v]);
}

static void Union(std::vector<int> &group, int u, int v) {
  group[Find(group, u)] = Find(group, v);
}

static void findSimilarRegion(std::vector<RegionTree *> &regions,
                              std::vector<Match> &matches) {
  std::unordered_set<RegionTree *> possible;

  int matchId = 0;
  std::vector<int> matchArr(regions.size() * regions.size());
  for (int i = 0; i < matchArr.size(); i++) {
    matchArr[i] = i;
  }
  for (int k = 0; k < 5; k++) {
    if (k) {
      regions.clear();
      for (RegionTree *it : possible) {
        std::vector<RegionTree *> childarr = it->getChild();
        if (childarr[0]->matchId < 0)
          continue;
        int id = Find(matchArr, childarr[0]->matchId);
        bool check = true;
        int level = 0;
        for (int i = 1; i < childarr.size(); i++) {
          if (childarr[i]->matchId < 0) {
            check = false;
            break;
          }
          level = std::max(level, childarr[i]->level);
        }
        if (check) {
          it->level = level + 1;
          // if (it->getRegion()->isSimple())
          regions.push_back(it);
        }
      }
    }
    if (regions.size() < 2)
      break;
    possible.clear();
    for (int i = 0; i < regions.size() - 1; i++) {
      for (int j = i + 1; j < regions.size(); j++) {
        Region *R1 = regions[i]->getRegion();
        Region *R2 = regions[j]->getRegion();
        RegionComparator RC(R1, R2);
        if (RC.compare()) {
          assert(regions[i]->level == regions[j]->level &&
                 "Region level must match!");
          std::shared_ptr<MergeableRegionPair> regionPair =
              std::make_shared<MergeableRegionPair>(*R1, *R2, RC);
          // errs() << "getSimilarityScore: " <<
          // regionPair->getSimilarityScore() << "\n";
          if (regionPair->getSimilarityScore() < scoreThreshold) {
            continue;
          }

          Match m = {.match = {regions[i], regions[j]},
                     .similarityScores = regionPair->getSimilarityScore(),
                     .level = regions[i]->level};
          matches.push_back(m);
          if (regions[i]->matchId >= 0 && regions[j]->matchId >= 0) {
            Union(matchArr, regions[i]->matchId, regions[j]->matchId);
          } else if (regions[i]->matchId >= 0) {
            regions[j]->matchId = regions[i]->matchId;
          } else if (regions[j]->matchId >= 0) {
            regions[i]->matchId = regions[j]->matchId;
          } else {
            regions[i]->matchId = regions[j]->matchId = matchId++;
          }
          possible.insert(regions[i]->getParent());
          possible.insert(regions[j]->getParent());
        }
      }
    }
  }
}

static void candidatesRanking(std::vector<Match> &matches) {
  auto cmp = [](const Match &v1, const Match &v2) {
    if (v1.level == v2.level) {
      return v1.similarityScores > v2.similarityScores;
    } else {
      return v1.level > v2.level;
    }
    // return v1.similarityScores > v2.similarityScores;
  };

  std::sort(matches.begin(), matches.end(), cmp);
}

static std::string GetValueName(const Value *V) {
  if (V) {
    std::string name;
    raw_string_ostream namestream(name);
    V->printAsOperand(namestream, false);
    return namestream.str();
  } else
    return "[null]";
}

static void StoreInstIntoAddr(Instruction *IV, Value *Addr) {
  IRBuilder<> Builder(IV->getParent());
  if (IV->isTerminator()) {
    BasicBlock *SrcBB = IV->getParent();
    if (auto *II = dyn_cast<InvokeInst>(IV)) {
      BasicBlock *DestBB = II->getNormalDest();

      Builder.SetInsertPoint(&*DestBB->getFirstInsertionPt());
      // create PHI
      PHINode *PHI = Builder.CreatePHI(IV->getType(), 0);
      for (auto PredIt = pred_begin(DestBB), PredE = pred_end(DestBB);
           PredIt != PredE; PredIt++) {
        BasicBlock *PredBB = *PredIt;
        if (PredBB == SrcBB) {
          PHI->addIncoming(IV, PredBB);
        } else {
          PHI->addIncoming(UndefValue::get(IV->getType()), PredBB);
        }
      }
      Builder.CreateStore(PHI, Addr);
    } else {
      for (auto SuccIt = succ_begin(SrcBB), SuccE = succ_end(SrcBB);
           SuccIt != SuccE; SuccIt++) {
        BasicBlock *DestBB = *SuccIt;

        Builder.SetInsertPoint(&*DestBB->getFirstInsertionPt());
        // create PHI
        PHINode *PHI = Builder.CreatePHI(IV->getType(), 0);
        for (auto PredIt = pred_begin(DestBB), PredE = pred_end(DestBB);
             PredIt != PredE; PredIt++) {
          BasicBlock *PredBB = *PredIt;
          if (PredBB == SrcBB) {
            PHI->addIncoming(IV, PredBB);
          } else {
            PHI->addIncoming(UndefValue::get(IV->getType()), PredBB);
          }
        }
        Builder.CreateStore(PHI, Addr);
      }
    }
  } else {
    Instruction *LastI = nullptr;
    Instruction *InsertPt = nullptr;
    for (Instruction &I : *IV->getParent()) {
      InsertPt = &I;
      if (LastI == IV)
        break;
      LastI = &I;
    }
    if (isa<PHINode>(InsertPt) || isa<LandingPadInst>(InsertPt)) {
      Builder.SetInsertPoint(&*IV->getParent()->getFirstInsertionPt());
      // Builder.SetInsertPoint(IV->getParent()->getTerminator());
    } else
      Builder.SetInsertPoint(InsertPt);

    Builder.CreateStore(IV, Addr);
  }
}

static AllocaInst *MemfyInst(Function *F, std::set<Instruction *> &InstSet) {
  BasicBlock *PreBB = &(F->getEntryBlock());
  if (InstSet.empty())
    return nullptr;
  IRBuilder<> Builder(&*PreBB->getFirstInsertionPt());
  AllocaInst *Addr = Builder.CreateAlloca((*InstSet.begin())->getType());

  errs() << "Storing in address:";
  Addr->dump();
  for (Instruction *I : InstSet) {
    errs() << "Instr:";
    I->dump();
    for (auto UIt = I->use_begin(), E = I->use_end(); UIt != E;) {
      Use &UI = *UIt;
      UIt++;

      auto *User = cast<Instruction>(UI.getUser());

      errs() << "User:";
      User->dump();

      Value *NewV = nullptr;
      if (auto *PHI = dyn_cast<PHINode>(User)) {
        /// TODO: make sure getOperandNo is getting the correct incoming edge
        auto InsertionPt =
            PHI->getIncomingBlock(UI.getOperandNo())->getTerminator();
        /// TODO: If the terminator of the incoming block is the producer of
        //        the value we want to store, the load cannot be inserted
        //        between the producer and the user. Something more complex is
        //        needed.
        // if (InsertionPt == I)
        //  continue;
        if (PHI->getIncomingBlock(UI.getOperandNo()) == I->getParent())
          continue;
        IRBuilder<> Builder(InsertionPt);
        // UI.set(Builder.CreateLoad(Addr->getType()->getPointerElementType(),
        // Addr));
        NewV = Builder.CreateLoad((*InstSet.begin())->getType(), Addr);
      } else {
        IRBuilder<> Builder(User);
        // UI.set(Builder.CreateLoad(Addr->getType()->getPointerElementType(),
        // Addr));
        NewV = Builder.CreateLoad((*InstSet.begin())->getType(), Addr);
      }
      errs() << "Load:";
      NewV->dump();
      UI.set(NewV);

      // errs() << "Memfying:\n";
      // NewV->dump();
      // UI.getUser()->dump();
    }
  }

  for (Instruction *I : InstSet)
    StoreInstIntoAddr(I, Addr);

  return Addr;
}

static bool commitChanges(Function *F) {

#ifdef TIME_STEPS_DEBUG
  TimeCodeGenFix.startTimer();
#endif

  Function *MergedFunc = F;

  std::vector<AllocaInst *> Allocas;

  std::list<Instruction *> LinearOffendingInsts;
  std::set<Instruction *> OffendingInsts;

  if (Debug) {
    errs() << "Collecting offending instructions\n";
  }

  // errs() << "Computing DT\n";
  DominatorTree DT(*MergedFunc);

  // errs() << "iterating over all instructions in function\n";
  for (Instruction &I : instructions(MergedFunc)) {
    if (auto *PHI = dyn_cast<PHINode>(&I)) {
      // errs() << "processing phi node\n";
      for (unsigned i = 0; i < PHI->getNumIncomingValues(); i++) {
        // errs() << "incoming value " << i << "\n";
        BasicBlock *BB = PHI->getIncomingBlock(i);
        if (BB == nullptr)
          errs() << "Null incoming block\n";
        Value *V = PHI->getIncomingValue(i);
        if (V == nullptr)
          errs() << "Null incoming value\n";
        if (auto *IV = dyn_cast<Instruction>(V)) {
          auto IncomingBlockTerm = BB->getTerminator();
          if (IncomingBlockTerm == nullptr) {
            // if (Debug)
            errs() << "ERROR: Null terminator\n";
            // MergedFunc->eraseFromParent();
#ifdef TIME_STEPS_DEBUG
            TimeCodeGenFix.stopTimer();
#endif
            return false;
          }
          // If the instruction IV producing the incoming value is not
          // dominated by the last instruction of the incoming block
          // (or IS the last instruction of the incoming block),
          // we will have to fix domination
          if (IncomingBlockTerm != IV) {
            if (!DT.dominates(IV, IncomingBlockTerm)) {
              if (OffendingInsts.count(IV) == 0) {
                OffendingInsts.insert(IV);
                LinearOffendingInsts.push_back(IV);
              }
            }
          }
        }
      }
    } else {
      // errs() << "processing other instructions\n";
      for (unsigned i = 0; i < I.getNumOperands(); i++) {
        // errs() << "operand " << i << "\n";
        if (I.getOperand(i) == nullptr) {
          // MergedFunc->dump();
          // I.getParent()->dump();
          // errs() << "Null operand\n";
          // I.dump();
          // if (Debug)
          errs() << "ERROR: Null operand\n";
          // MergedFunc->eraseFromParent();
#ifdef TIME_STEPS_DEBUG
          TimeCodeGen.stopTimer();
#endif
          return false;
        }
        if (auto *IV = dyn_cast<Instruction>(I.getOperand(i))) {
          if (!DT.dominates(IV, &I)) {
            if (OffendingInsts.count(IV) == 0) {
              OffendingInsts.insert(IV);
              LinearOffendingInsts.push_back(IV);
            }
          }
        }
      }
    }
  }

  auto isCoalescingProfitable = [&](Instruction *I1, Instruction *I2) -> bool {
    std::set<BasicBlock *> BBSet1;
    std::set<BasicBlock *> UnionBB;
    for (User *U : I1->users()) {
      if (auto *UI = dyn_cast<Instruction>(U)) {
        BasicBlock *BB1 = UI->getParent();
        BBSet1.insert(BB1);
        UnionBB.insert(BB1);
      }
    }

    unsigned Intersection = 0;
    for (User *U : I2->users()) {
      if (auto *UI = dyn_cast<Instruction>(U)) {
        BasicBlock *BB2 = UI->getParent();
        UnionBB.insert(BB2);
        if (BBSet1.find(BB2) != BBSet1.end())
          Intersection++;
      }
    }

    const float Threshold = 0.7;
    return (float(Intersection) / float(UnionBB.size()) > Threshold);
  };

  auto OptimizeCoalescing =
      [&](Instruction *I, std::set<Instruction *> &InstSet,
          std::map<Instruction *, std::map<Instruction *, unsigned>>
              &CoalescingCandidates,
          std::set<Instruction *> &Visited) {
        Instruction *OtherI = nullptr;
        unsigned Score = 0;
        if (CoalescingCandidates.find(I) != CoalescingCandidates.end()) {
          for (auto &Pair : CoalescingCandidates[I]) {
            if (Pair.second > Score &&
                Visited.find(Pair.first) == Visited.end()) {
              if (isCoalescingProfitable(I, Pair.first)) {
                OtherI = Pair.first;
                Score = Pair.second;
              }
            }
          }
        }
        /*
        if (OtherI==nullptr) {
          for (Instruction *OI : OffendingInsts) {
            if (OI->getType()!=I->getType()) continue;
            if (Visited.find(OI)!=Visited.end()) continue;
            if (CoalescingCandidates.find(OI)!=CoalescingCandidates.end())
        continue; if( (BlocksF2.find(I->getParent())==BlocksF2.end() &&
        BlocksF1.find(OI->getParent())==BlocksF1.end()) ||
                (BlocksF2.find(OI->getParent())==BlocksF2.end() &&
        BlocksF1.find(I->getParent())==BlocksF1.end()) ) { OtherI = OI; break;
            }
          }
        }
        */
        if (OtherI) {
          InstSet.insert(OtherI);
          // errs() << "Coalescing: " << GetValueName(I->getParent()) << ":";
          // I->dump(); errs() << "With: " << GetValueName(OtherI->getParent())
          // << ":"; OtherI->dump();
        }
      };

  if (Debug) {
    errs() << "Finishing code\n";
  }
  if (MergedFunc != nullptr) {
    // errs() << "Offending: " << OffendingInsts.size() << " ";
    // errs() << ((float)OffendingInsts.size())/((float)AlignedSeq.size()) << "
    // : "; if (OffendingInsts.size()>1000) { if (false) {
    /*
    if (((float)OffendingInsts.size()) / ((float)AlignedSeq.size()) > 4.5) {
      if (Debug)
        errs() << "Bailing out\n";
#ifdef TIME_STEPS_DEBUG
      TimeCodeGenFix.stopTimer();
#endif
      return false;
    }
    */
    if (Debug) {
      errs() << "Fixing Domination\n";
      errs() << "LinearOffendingInsts: " << LinearOffendingInsts.size() << '\n';
      // MergedFunc->dump();
    }
    std::set<Instruction *> Visited;
    for (Instruction *I : LinearOffendingInsts) {
      if (Visited.find(I) != Visited.end())
        continue;

      errs() << "Processing: ";
      I->dump();

      std::set<Instruction *> InstSet;
      InstSet.insert(I);

      // Create a coalescing group in InstSet
      // if (EnableSALSSACoalescing) {
      //   errs() << "optimizing coalescing\n";
      //   OptimizeCoalescing(I, InstSet, CoalescingCandidates, Visited);
      //   errs() << "done coalescing\n";
      // }

      for (Instruction *OtherI : InstSet)
        Visited.insert(OtherI);

      errs() << "Computing memfyInst\n";
      AllocaInst *Addr = MemfyInst(F, InstSet);
      errs() << "Addr computed: ";
      Addr->dump();
      if (Addr)
        Allocas.push_back(Addr);

      errs() << "next\n";
    }

    if (Allocas.size() > 3) {
      return false;
    }

    // MergedFunc->dump();

    errs() << "verifying\n";
    if (verifyFunction(*MergedFunc)) {
      // if (Verbose)
      errs() << "ERROR: Produced Broken Function!\n";
#ifdef TIME_STEPS_DEBUG
      TimeCodeGenFix.stopTimer();
#endif
      return false;
    }

    errs() << "Building DT\n";
    DominatorTree DT(*MergedFunc);

    errs() << "Mem2Reg\n";
    PromoteMemToReg(Allocas, DT, nullptr);

    // MergedFunc->dump();

    errs() << "verifying\n";
    if (verifyFunction(*MergedFunc)) {
      // if (Verbose)
      errs() << "ERROR: Produced Broken Function!\n";
#ifdef TIME_STEPS_DEBUG
      TimeCodeGenFix.stopTimer();
#endif
      return false;
    }
#ifdef TIME_STEPS_DEBUG
    TimeCodeGenFix.stopTimer();
#endif
#ifdef TIME_STEPS_DEBUG
    TimePostOpt.startTimer();
#endif
#ifdef TIME_STEPS_DEBUG
    TimePostOpt.stopTimer();
#endif
    // MergedFunc->dump();
  }

  return MergedFunc != nullptr;
}

static Function *regionMerging(Function *F, DominatorTree &DT,
                               PostDominatorTree &PDT, LoopInfo &LI,
                               TargetTransformInfo &TTI, Match &match) {
  auto it = match.match;

  if (it.first->matchId > 0)
    it.first->matchId = 0;

  if (it.second->matchId > 0)
    it.second->matchId = 0;

  it.first->matchId--;
  it.second->matchId--;

  if (it.first->matchId < -2 || it.second->matchId < -2) {
    return F;
  }

#ifdef ENABLE_TIMING
  auto T1 = std::chrono::high_resolution_clock::now();
  auto T2 = std::chrono::high_resolution_clock::now();
  auto micros =
      std::chrono::duration_cast<std::chrono::microseconds>(T2 - T1).count();
#endif

#ifdef ENABLE_TIMING
  T1 = std::chrono::high_resolution_clock::now();
#endif

  ValueToValueMapTy vmap;
  Function *F_new = CloneFunction(F, vmap);
  std::string Name = F->getName().str();
  int SizeOrig = 0;
  int SizeAfter = 0;
  DT.recalculate(*F_new);
  PDT.recalculate(*F_new);

  SizeOrig = EstimateFunctionSize(F, TTI);

  if (!it.first->EntryBlock->getParent() || 
      !it.first->ExitBlock->getParent() ||
      !it.second->EntryBlock->getParent() ||
      !it.second->ExitBlock->getParent()) {
    F_new->eraseFromParent();
    return F;
  }

  BasicBlock *clonedLeftEntry = cast<BasicBlock>(vmap[it.first->EntryBlock]);
  BasicBlock *clonedLeftExit = cast<BasicBlock>(vmap[it.first->ExitBlock]);
  BasicBlock *clonedRightEntry = cast<BasicBlock>(vmap[it.second->EntryBlock]);
  BasicBlock *clonedRightExit = cast<BasicBlock>(vmap[it.second->ExitBlock]);

  Region *RegionL = NULL;
  Region *RegionR = NULL;
  ControlFlowGraphInfo CFGInfo(*F_new, DT, PDT, TTI);
  RegionInfo *RI = CFGInfo.getRegionInfo().get();

  if (clonedLeftEntry && clonedLeftExit) {
    RegionL = Utils::getRegionWithEntryExit(*RI, clonedLeftEntry,
                                            clonedLeftExit);
  }

  if (clonedRightEntry && clonedRightExit) {
    RegionR = Utils::getRegionWithEntryExit(*RI, clonedRightEntry,
                                            clonedRightExit);
  }

#ifdef ENABLE_TIMING
  T2 = std::chrono::high_resolution_clock::now();
  micros =
      std::chrono::duration_cast<std::chrono::microseconds>(T2 - T1).count();
  getRegionTime += (unsigned int)(micros);
#endif

  if (!RegionL || !RegionR) {
    regionNotExistNum++;
    F_new->eraseFromParent();
    return F;
  }

  RegionL->dump();
  RegionR->dump();

  RegionComparator RC(RegionL, RegionR);
  if (!RC.compare()) {
    F_new->eraseFromParent();
    return F;
  }

  if (RegionL->getEntry() == RegionR->getExit() ||
      RegionL->getExit() == RegionR->getEntry()) {
    adjacentRegionNum++;
    F_new->eraseFromParent();
    return F;
  }

  // bool bfcase = false;
  // Region *parent = RI->getCommonRegion(RegionL, RegionR);
  // if (parent->getEntry()->getTerminator()->getNumSuccessors() == 2) {
  //   BasicBlock *LeftEntry =
  //       parent->getEntry()->getTerminator()->getSuccessor(0);
  //   BasicBlock *RightEntry =
  //       parent->getEntry()->getTerminator()->getSuccessor(1);
  //   if (DT.dominates(LeftEntry, RegionL->getEntry()) &&
  //       PDT.dominates(RegionL->getEntry(), LeftEntry) &&
  //       DT.dominates(RightEntry, RegionR->getEntry()) &&
  //       PDT.dominates(RegionR->getEntry(), RightEntry)) {
  //     bfcase = true;
  //   } else if (DT.dominates(LeftEntry, RegionR->getEntry()) &&
  //              PDT.dominates(RegionR->getEntry(), LeftEntry) &&
  //              DT.dominates(RightEntry, RegionL->getEntry()) &&
  //              PDT.dominates(RegionL->getEntry(), RightEntry)) {
  //     bfcase = true;
  //   }
  // }

  // if (!enableBfcase && bfcase) {
  //   return F;
  // }

  

  SESERegion LeftR(RegionL);
  SESERegion RightR(RegionR);

  int SizeLeft = 0;
  int SizeRight = 0;

  std::set<BasicBlock *> KnownBBs;
  for (BasicBlock &BB : LeftR) {
    KnownBBs.insert(&BB);

    for (Instruction &I : BB) {
      auto cost = TTI.getInstructionCost(
          &I, TargetTransformInfo::TargetCostKind::TCK_CodeSize);
      SizeLeft += cost.getValue().value();
      // SizeLeft++;
    }
  }
  for (BasicBlock &BB : RightR) {
    KnownBBs.insert(&BB);

    for (Instruction &I : BB) {
      auto cost = TTI.getInstructionCost(
          &I, TargetTransformInfo::TargetCostKind::TCK_CodeSize);
      SizeRight += cost.getValue().value();
      // SizeRight++;
    }
  }

  bool UseCostInFingerprint = true;
  AlignmentStats TotalAlignmentStats;
#ifdef ENABLE_TIMING
  T1 = std::chrono::high_resolution_clock::now();
#endif
  AlignedSequence<Value *> AlignedInsts =
      FunctionMerger::alignBlocks(LeftR, RightR, TotalAlignmentStats,
                                  (UseCostInFingerprint ? (&TTI) : nullptr));
#ifdef ENABLE_TIMING
  T2 = std::chrono::high_resolution_clock::now();
  micros =
      std::chrono::duration_cast<std::chrono::microseconds>(T2 - T1).count();
  alignBlocksTime += (unsigned int)(micros);
#endif

  // for (auto &Entry : AlignedInsts) {

  //   if (true) {
  //     errs() << "-----------------------------------------------------\n";
  //     if (Entry.get(0)) {
  //       if (isa<BasicBlock>(Entry.get(0)))
  //         errs() << Entry.get(0)->getName() << "\n";
  //       else
  //         Entry.get(0)->dump();
  //     } else
  //       errs() << "\t-\n";
  //     if (Entry.get(1)) {
  //       if (isa<BasicBlock>(Entry.get(1)))
  //         errs() << Entry.get(1)->getName() << "\n";
  //       else
  //         Entry.get(1)->dump();
  //     } else {
  //       errs() << "\t-\n";
  //     }
  //   }
  // }

  LLVMContext &Context = F_new->getContext();
  const DataLayout *DL = &F_new->getParent()->getDataLayout();
  Type *IntPtrTy = DL->getIntPtrType(Context);

  ValueToValueMapTy VMap;
  // initialize VMap
  for (Argument &Arg : F_new->args()) {
    VMap[&Arg] = &Arg;
  }

  for (BasicBlock &BB : *F_new) {
    if (KnownBBs.count(&BB))
      continue;
    VMap[&BB] = &BB;
    for (Instruction &I : BB) {
      VMap[&I] = &I;
    }
  }

#ifdef ENABLE_TIMING
  T1 = std::chrono::high_resolution_clock::now();
#endif

  FunctionMergingOptions Options = FunctionMergingOptions()
                                       .enableUnifiedReturnTypes(false)
                                       .matchOnlyIdenticalTypes(true);

  BasicBlock *EntryBB = BasicBlock::Create(Context, "rgmEntry", F_new);
  BasicBlock *LBB = RegionL->getEntry();
  BasicBlock *RBB = RegionR->getEntry();
  IRBuilder<> builder(EntryBB);
  PHINode *labelPhiNode =
      builder.CreatePHI(Type::getInt1Ty(F_new->getContext()), 2);
  labelPhiNode->addIncoming(ConstantInt::get(Type::getInt1Ty(Context), 1), LBB);
  labelPhiNode->addIncoming(ConstantInt::get(Type::getInt1Ty(Context), 0), RBB);
  FunctionMerger::SALSSACodeGen CG(LeftR.Blocks, RightR.Blocks);
  CG.insert(labelPhiNode);
  CG.setFunctionIdentifier(labelPhiNode)
      .setEntryPoints(LBB, RBB)
      .setReturnTypes(F_new->getReturnType(), F_new->getReturnType())
      .setMergedFunction(F_new)
      .setMergedEntryPoint(EntryBB)
      .setMergedReturnType(F_new->getReturnType(), false)
      .setContext(&Context)
      .setIntPtrType(IntPtrTy);
  if (!CG.generate(AlignedInsts, VMap, Options)) {
    errs() << "ERROR: Failed to generate the fused branches!\n";
    if (Debug) {
      errs() << "Destroying generated code\n";
    }
    CG.destroyGeneratedCode();
    if (Debug) {
      errs() << "Generated code destroyed\n";
    }
    EntryBB->eraseFromParent();
    if (Debug) {
      errs() << "Branch fusion reversed\n";
    }
    F_new->eraseFromParent();
    mergeGenFailNum++;
    return F;
  }

#ifdef ENABLE_TIMING
  T2 = std::chrono::high_resolution_clock::now();
  micros =
      std::chrono::duration_cast<std::chrono::microseconds>(T2 - T1).count();
  mergeGenTime += (unsigned int)(micros);
#endif

  std::map<PHINode *, PHINode *> ReplacedPHIs;

  auto ProcessPHIs = [&](auto ExitSet,
                         std::set<BasicBlock *> &VisitedBB) -> bool {
    for (BasicBlock &BB : ExitSet) {
      if (VisitedBB.count(&BB))
        continue;
      VisitedBB.insert(&BB);

      auto PHIs = BB.phis();

      for (auto It = PHIs.begin(), E = PHIs.end(); It != E;) {
        PHINode *PHI = &*It;
        It++;

        if (Debug) {
          errs() << "Solving PHI node:";
          PHI->dump();
        }

        IRBuilder<> Builder(PHI);
        PHINode *NewPHI = Builder.CreatePHI(PHI->getType(), 0);
        CG.insert(NewPHI);
        VMap[PHI] = NewPHI;
        ReplacedPHIs[PHI] = NewPHI;

        // Same block can be a predecessor multiple times and can have multiple
        // incoming edges into BB To keep BB's predecessor information
        // consistent with the phi incoming values, we need to keep track of the
        // number of incoming edges from each predecessor block
        // std::map<BasicBlock *, std::map<BasicBlock *, Value *>> NewEntries;
        std::map<BasicBlock *, std::map<BasicBlock *, std::pair<Value *, int>>>
            NewEntries;
        std::set<BasicBlock *> OldEntries;
        for (unsigned i = 0; i < PHI->getNumIncomingValues(); i++) {
          BasicBlock *InBB = PHI->getIncomingBlock(i);
          if (KnownBBs.count(InBB)) {
            Value *NewV = PHI->getIncomingValue(i);
            auto Pair = CG.getNewEdge(InBB, &BB);
            BasicBlock *NewBB = Pair.first;
            if (Instruction *OpI =
                    dyn_cast<Instruction>(PHI->getIncomingValue(i))) {
              NewV = VMap[OpI];

              if (NewV == nullptr) {
                errs() << "ERROR: Null mapped value!\n";
                return false;
              }
            }
            auto result_pair = NewEntries[NewBB].insert({InBB, {NewV, 1}});
            if (!result_pair.second)
              result_pair.first->second.second++;
            // NewEntries[NewBB][InBB] = NewV;
            OldEntries.insert(InBB);
          } else {
            // simply copy incoming values from outside the two regions being
            // merged
            NewPHI->addIncoming(PHI->getIncomingValue(i),
                                PHI->getIncomingBlock(i));
          }
        }

        if (Debug) {
          errs() << "Num entries: " << NewEntries.size() << "\n";
          for (auto &Pair : NewEntries) {
            errs() << "Incoming Block: " << Pair.first->getName().str() << "\n";
            for (auto &Pair2 : Pair.second) {
              errs() << "Block: " << Pair2.first->getName().str() << " -> ";
              Pair2.second.first->dump();
            }
          }
        }

        if (Debug) {
          errs() << "Creating New PHI\n";
          PHI->dump();
        }
        for (auto &Pair : NewEntries) {
          if (Debug) {
            errs() << "Incoming Block: " << Pair.first->getName().str() << "\n";
          }
          if (Pair.second.size() == 1) {
            auto &InnerPair = *(Pair.second.begin());
            Value *V = InnerPair.second.first;
            int repeats = InnerPair.second.second;
            for (int i = 0; i < repeats; ++i)
              NewPHI->addIncoming(V, Pair.first);
          } else if (Pair.second.size() == 2) {
            /*
            Values that were originally coming from different basic blocks that
            have been merged must be properly handled. In this case, we add a
            selection in the merged incomming block to produce the correct value
            for the phi node.
            */
            if (Debug) {
              errs() << "Found  PHI incoming from two different blocks\n";
            }
            Value *LeftV = nullptr;
            Value *RightV = nullptr;
            int repeats = 0;
            for (auto &InnerPair : Pair.second) {
              if (LeftR.contains(InnerPair.first)) {
                if (Debug) {
                  errs() << "Value coming from the Left block: "
                         << GetValueName(InnerPair.first) << " : ";
                  InnerPair.second.first->dump();
                }
                LeftV = InnerPair.second.first;
              }
              if (RightR.contains(InnerPair.first)) {
                if (Debug) {
                  errs() << "Value coming from the Right block: "
                         << GetValueName(InnerPair.first) << " : ";
                  InnerPair.second.first->dump();
                }
                RightV = InnerPair.second.first;
              }
              repeats = repeats > InnerPair.second.second
                            ? repeats
                            : InnerPair.second.second;
            }

            if (LeftV && RightV) {
              Value *MergedV = LeftV;
              if (LeftV != RightV) {
                IRBuilder<> Builder(Pair.first->getTerminator());
                // TODO: handle if one of the values is the terminator itself!
                MergedV = Builder.CreateSelect(labelPhiNode, LeftV, RightV);
                if (SelectInst *SelI = dyn_cast<SelectInst>(MergedV))
                  CG.insert(SelI);
              }
              for (int i = 0; i < repeats; ++i)
                NewPHI->addIncoming(MergedV, Pair.first);
            } else {
              errs() << "ERROR: THIS IS WEIRD! MAYBE IT SHOULD NOT BE HERE!\n";
              return false;
            }
          } else {
            errs() << "ERROR: THIS IS WEIRD! MAYBE IT SHOULD NOT BE HERE!\n";
            return false;
            /*
            IRBuilder<> Builder(&*F.getEntryBlock().getFirstInsertionPt());
            AllocaInst *Addr = Builder.CreateAlloca(PHI->getType());
            CG.insert(Addr);

            for (Value *V : Pair.second) {
              if (Instruction *OpI = dyn_cast<Instruction>(V)) {
                CG.StoreInstIntoAddr(OpI, Addr);
              } else {
                errs() << "ERROR: must also handle non-instruction values "
                          "via a select\n";
              }
            }

            Builder.SetInsertPoint(Pair.first->getTerminator());
            Value *LI = Builder.CreateLoad(PHI->getType(), Addr);

            PHI->addIncoming(LI, Pair.first);
      */
          }
        }

        /*
        unsigned CountPreds = 0;
        for (auto It = pred_begin(&BB), E = pred_end(&BB); It != E; It++) {
          BasicBlock *PredBB = *It;

          if (!LeftR.contains(PredBB) && !RightR.contains(PredBB)) {
                  CountPreds++;
                  errs() << "+PredBB: " << PredBB->getName().str() << "\n";
          } else {
                  errs() << "-PredBB: " << PredBB->getName().str() << "\n";
          }
        }
        if (CountPreds!=NewPHI->getNumIncomingValues()) {
                errs() << "ERROR: unexpected number of predecessor\n";
        }
        */

        if (Debug) {
          errs() << "Resulting PHI node:";
          NewPHI->dump();
        }
      }
    }
    return true;
  };

  bool Error = false;

  std::set<BasicBlock *> VisitedBB;
  Error = Error || !ProcessPHIs(LeftR.exits(), VisitedBB);
  Error = Error || !ProcessPHIs(RightR.exits(), VisitedBB);

  if (Debug) {
    errs() << "Modified function\n";
  }

  double MergedSize = 0;
  int rgs = 0;
  if (Debug) {
    errs() << "Computing size...\n";
  }
  for (Instruction *I : CG) {
    auto cost = TTI.getInstructionCost(
        I, TargetTransformInfo::TargetCostKind::TCK_CodeSize);
    MergedSize += cost.getValue().value();
    rgs++;
    // MergedSize++;
    // errs() << cost.getValue().value() << " ";
    // I->dump();
    if (BranchInst *BI = dyn_cast<BranchInst>(I)) {
      if (BI->isConditional() && BI->getSuccessor(0) == BI->getSuccessor(1)) {
        MergedSize -= matchArg;
        rgs--;
      }
    } else if (PHINode *BI = dyn_cast<PHINode>(I)) {
      MergedSize += 0.2;
    }
  }

  if (Debug) {
    errs() << "SizeLeft: " << SizeLeft << "\n";
    errs() << "SizeRight: " << SizeRight << "\n";
    errs() << "Original Size: " << (SizeLeft + SizeRight) << "\n";
    errs() << "New Size: " << MergedSize << "\n";
  }

  errs() << "SizeDiff: " << (SizeLeft + SizeRight) << " X " << MergedSize
         << " : " << ((int)(SizeLeft + SizeRight) - ((int)MergedSize)) << " : ";

  bool Profitable = MergedSize < SizeLeft + SizeRight;

  if (Error) {
    ProcessPHIsErrorNum++;
  }

  if (!Profitable) {
    notProfitableLocalNum++;
    // if (match.similarityScores <= 0.45) {
    //   int num;
    //   num =
    //   readCounter("/home/smallhanley/sslab/work/benchmark/SPEC/fileLessFail");
    //   num++;
    //   writeCounter("/home/smallhanley/sslab/work/benchmark/SPEC/fileLessFail",
    //   num);
    // }
    // else {
    //   int num;
    //   num =
    //   readCounter("/home/smallhanley/sslab/work/benchmark/SPEC/fileMoreFail");
    //   num++;
    //   writeCounter("/home/smallhanley/sslab/work/benchmark/SPEC/fileMoreFail",
    //   num);
    // }
  }

#ifdef ENABLE_TIMING
  T1 = std::chrono::high_resolution_clock::now();
#endif

  if (Error || !Profitable) {
    if (Debug) {
      errs() << "Destroying generated code\n";
    }

    // F.dump();
    CG.destroyGeneratedCode();
    if (Debug) {
      errs() << "Generated code destroyed\n";
    }
    EntryBB->eraseFromParent();
    if (Debug) {
      errs() << "Branch fusion reversed\n";
    }
    F_new->eraseFromParent();
    return F;
  }

#ifdef ENABLE_TIMING
  T2 = std::chrono::high_resolution_clock::now();
  micros =
      std::chrono::duration_cast<std::chrono::microseconds>(T2 - T1).count();
  resumeCodeTime += (unsigned int)(micros);
#endif

  std::vector<Instruction *> DeadInsts;

  for (auto &Pair : ReplacedPHIs) {
    Pair.first->replaceAllUsesWith(Pair.second);
    Pair.first->dropAllReferences();
    DeadInsts.push_back(Pair.first);
  }

  // errs() << "Before deleting the old code\n";
  // F.dump();
  for (BasicBlock *BB : KnownBBs) {
    for (Instruction &I : *BB) {
      I.replaceAllUsesWith(VMap[&I]);

      I.dropAllReferences();
      DeadInsts.push_back(&I);
    }
  }
  for (Instruction *I : DeadInsts) {
    // if (BranchInst *BI = dyn_cast<BranchInst>(I)) {
    //   ListBIs.remove(BI);
    // }
    I->eraseFromParent();
  }
  for (BasicBlock *BB : KnownBBs) {
    if (BB == LBB || BB == RBB)
      continue;
    BB->eraseFromParent();
  }

  builder.SetInsertPoint(LBB);
  Instruction *NewBrL = builder.CreateBr(EntryBB);
  builder.SetInsertPoint(RBB);
  Instruction *NewBrR = builder.CreateBr(EntryBB);

  if (Debug) {
    errs() << "After deleting the old code\n";
    // F->dump();
  }
  if (!commitChanges(F_new)) {
    // F.dump();
    errs() << "ERROR: committing final changes to the fused branches "
              "!!!!!!!\n";
    F_new->eraseFromParent();
    commitChangesErrorNum++;
    return F;
  }
  if (Debug) {
    errs() << "Final version\n";
    // F.dump();
  }

  SimplifyCFGOptions SimplifyCFGOptionsObj;

  simplifyFunction(*F_new, TTI,
                   SimplifyCFGOptionsObj.setSimplifyCondBranch(false)
                       .sinkCommonInsts(false)
                       .hoistCommonInsts(false));

  SizeAfter = EstimateFunctionSize(F_new, TTI);

  if (Debug) {
    errs() << "*SizeOrig: " << SizeOrig << "\n";
    errs() << "*SizeAfter: " << SizeAfter << "\n";
  }

  if (SizeAfter < SizeOrig - matchThreshold && rgs > regionSizeThreshold) {
    errs() << "RGMSuccess\n";
    it.first->EntryBlock = clonedLeftEntry;
    it.first->ExitBlock = clonedLeftExit;
    it.second->EntryBlock = clonedRightEntry;
    it.second->ExitBlock = clonedRightExit;
    F->replaceAllUsesWith(F_new);
    F->eraseFromParent();
    F_new->setName(Name);
    DT.recalculate(*F_new);
    PDT.recalculate(*F_new);
    mergeRegionPairsNum++;
    regionSize += (SizeOrig - SizeAfter) * 100.0 / SizeOrig;
    // hasBranchFusion = hasBranchFusion || bfcase;
    // regionSize += MergedSize;
    // if (match.similarityScores <= 0.45) {
    //   int num;
    //   num =
    //   readCounter("/home/smallhanley/sslab/work/benchmark/SPEC/fileLessSucc");
    //   num++;
    //   writeCounter("/home/smallhanley/sslab/work/benchmark/SPEC/fileLessSucc",
    //   num);
    // }
    // else {
    //   int num;
    //   num =
    //   readCounter("/home/smallhanley/sslab/work/benchmark/SPEC/fileMoreSucc");
    //   num++;
    //   writeCounter("/home/smallhanley/sslab/work/benchmark/SPEC/fileMoreSucc",
    //   num);
    // }
    return F_new;
  } else {
    F_new->eraseFromParent();
    DT.recalculate(*F);
    PDT.recalculate(*F);
    notProfitableGlobalNum++;
    // if (match.similarityScores <= 0.45) {
    //   int num;
    //   num =
    //   readCounter("/home/smallhanley/sslab/work/benchmark/SPEC/fileLessFail");
    //   num++;
    //   writeCounter("/home/smallhanley/sslab/work/benchmark/SPEC/fileLessFail",
    //   num);
    // }
    // else {
    //   int num;
    //   num =
    //   readCounter("/home/smallhanley/sslab/work/benchmark/SPEC/fileMoreFail");
    //   num++;
    //   writeCounter("/home/smallhanley/sslab/work/benchmark/SPEC/fileMoreFail",
    //   num);
    // }
    return F;
  }
}

static bool runImplCodeSize(Function &F, DominatorTree &DT,
                            PostDominatorTree &PDT, LoopInfo &LI,
                            TargetTransformInfo &TTI) {
  INFO << "Procesing function : " << F.getName() << "\n";
  Function *Func = &F;
  bool LocalChange = false, Changed = false;

  int OrigCodeSize = EstimateFunctionSize(&F, TTI);
  unsigned CountIter = 0;

  do {
    CountIter++;

    LocalChange = false;
    for (BasicBlock *BB : post_order(&Func->getEntryBlock())) {
      if (Utils::isValidMergeLocation(*BB, DT, PDT)) {
        INFO << "Valid merge location found at block "
             << BB->getNameOrAsOperand() << "\n";
        ControlFlowGraphInfo CFGInfo(*Func, DT, PDT, TTI);
        RegionAnalyzer RA(BB, CFGInfo);
        RA.computeRegionMatch();

        if (RA.hasAnyProfitableMatch()) {

          // Store the indexes of profitable merges
          SmallVector<int, 8> Profitable;

          // clone function
          ValueToValueMapTy VMap;
          Function *ClonedFunc = CloneFunction(Func, VMap);
          DominatorTree ClonedDT(*ClonedFunc);
          PostDominatorTree ClonedPDT(*ClonedFunc);
          ControlFlowGraphInfo ClonedCFGInfo(*ClonedFunc, ClonedDT, ClonedPDT,
                                             TTI);

          RegionAnalyzer ClonedRA(dyn_cast<BasicBlock>(VMap[BB]),
                                  ClonedCFGInfo);
          ClonedRA.computeRegionMatch();

          for (unsigned I = 0; I < ClonedRA.regionMatchSize(); ++I) {
            if (!ClonedRA.isRegionMatchProfitable(I))
              continue;

            int SizeBefore = EstimateFunctionSize(ClonedFunc, TTI);
            RegionMelder ClonedRM(ClonedRA);
            ClonedRM.merge(I);
            int SizeAfter = EstimateFunctionSize(ClonedFunc, TTI);
            DEBUG << "Size changed from " << SizeBefore << " to " << SizeAfter
                  << " : " << (SizeBefore - SizeAfter) << " : "
                  << ((SizeBefore > SizeAfter) ? "Profitable" : "Unprofitable")
                  << " Branch Fusion! [" << F.getName().str() << "] ";
            BB->getTerminator()->dump();
            if (SizeBefore > SizeAfter) {
              Profitable.push_back(I);
            }
          }

          // If there are profitble merges perform them on Func
          if (!Profitable.empty()) {
            for (int I : Profitable) {
              RegionMelder RM(RA);
              RM.merge(I);
            }
            LocalChange = true;
          }

          // delete the cloned functon
          ClonedFunc->eraseFromParent();

          if (LocalChange) {
            DT.recalculate(*Func);
            PDT.recalculate(*Func);
            break;
          }
        }
      }
    }

    Changed |= LocalChange;

  } while (LocalChange); // && CountIter < MaxIterations);

  if (Changed) {
    // simplifyFunction(
    //             *Func, TTI,
    //             SimplifyCFGOptionsObj.setSimplifyCondBranch(false));

    int FinalCodeSize = EstimateFunctionSize(&F, TTI);
    double PercentReduction =
        (OrigCodeSize - FinalCodeSize) * 100 / (double)OrigCodeSize;
    INFO << "Size reduction for function " << F.getName() << ": "
         << OrigCodeSize << " to  " << FinalCodeSize << " (" << PercentReduction
         << "%)"
         << "\n";
  }

  return Changed;
}

static void runImpl(Function *F, DominatorTree &DT, PostDominatorTree &PDT,
                    LoopInfo &LI, TargetTransformInfo &TTI) {

  // if (F->getName() != "MogrifyImageCommand") {
  //   return;
  // }
  // runAnalysisOnly(F, DT, PDT, LI, TTI);
  std::vector<RegionTree *> regions;
#ifdef ENABLE_TIMING
  auto T1 = std::chrono::high_resolution_clock::now();
  auto T2 = std::chrono::high_resolution_clock::now();
  auto micros =
      std::chrono::duration_cast<std::chrono::microseconds>(T2 - T1).count();
#endif

  // runImplCodeSize(*F, DT, PDT, LI, TTI);

#ifdef ENABLE_TIMING
  T1 = std::chrono::high_resolution_clock::now();
#endif
  runRegionMatch(*F, DT, PDT, LI, TTI, regions);
#ifdef ENABLE_TIMING
  T2 = std::chrono::high_resolution_clock::now();
  micros =
      std::chrono::duration_cast<std::chrono::microseconds>(T2 - T1).count();
  runRegionMatchTime += (unsigned int)(micros);
#endif
  // melding(F, DT, PDT, LI, TTI);
  std::vector<Match> matches;
#ifdef ENABLE_TIMING
  T1 = std::chrono::high_resolution_clock::now();
#endif
  findSimilarRegion(regions, matches);
#ifdef ENABLE_TIMING
  T2 = std::chrono::high_resolution_clock::now();
  micros =
      std::chrono::duration_cast<std::chrono::microseconds>(T2 - T1).count();
  findSimilarRegionTime += (unsigned int)(micros);
#endif
#ifdef ENABLE_TIMING
  T1 = std::chrono::high_resolution_clock::now();
#endif
  candidatesRanking(matches);
#ifdef ENABLE_TIMING
  T2 = std::chrono::high_resolution_clock::now();
  micros =
      std::chrono::duration_cast<std::chrono::microseconds>(T2 - T1).count();
  candidatesRankingTime += (unsigned int)(micros);
#endif

  for (auto &match : matches) {
    auto it = match.match;
    it.first->getRegion()->dump();
    errs() << "------------\n";
    it.second->getRegion()->dump();
    // RegionComparator RC(it.first, it.second);
    // RC.compare();
    // std::shared_ptr<MergeableRegionPair> regionPair =
    //     std::make_shared<MergeableRegionPair>(*it.first, *it.second, RC);
    // errs() << "Regions are similar\n";
    //   errs() << *regionPair << "\n";
    //   errs() << "Similarity score is " << regionPair->getSimilarityScore()
    //         << "\n";
    errs() << "============\n";
  }

  // matchedRegionPairsNum += matches.size();

  int i = 0;
  for (auto &match : matches) {
    if (i++ > matches.size() * matchRatio)
      break;
    // if (i++ > 20)
    //   break;
    errs() << "similarityScores: " << match.similarityScores << '\n';
    matchedRegionPairsNum++;
#ifdef ENABLE_TIMING
    T1 = std::chrono::high_resolution_clock::now();
#endif
    F = regionMerging(F, DT, PDT, LI, TTI, match);
#ifdef ENABLE_TIMING
    T2 = std::chrono::high_resolution_clock::now();
    micros =
        std::chrono::duration_cast<std::chrono::microseconds>(T2 - T1).count();
    regionMergingTime += (unsigned int)(micros);
#endif
  }
  // SimplifyCFGOptions SimplifyCFGOptionsObj;
  // FunctionPassManager FPM;
  // if (simplifyFunction(*F, TTI,
  //                      SimplifyCFGOptionsObj.setSimplifyCondBranch(false)
  //                          .sinkCommonInsts(false)
  //                          .hoistCommonInsts(false))) {
  //   DT.recalculate(*F);
  //   PDT.recalculate(*F);
  // }
}

PreservedAnalyses RegionMergingPass::run(Function &F,
                                         FunctionAnalysisManager &FAM) {
  errs() << "Running function: " << F.getName() << "\n";

  auto &DT = FAM.getResult<DominatorTreeAnalysis>(F);
  auto &PDT = FAM.getResult<PostDominatorTreeAnalysis>(F);
  auto &TTI = FAM.getResult<TargetIRAnalysis>(F);
  auto &LI = FAM.getResult<LoopAnalysis>(F);

  runImpl(&F, DT, PDT, LI, TTI);

  return PreservedAnalyses::none();
}

PreservedAnalyses RegionMergingModulePass::run(Module &M,
                                               ModuleAnalysisManager &MAM) {
  auto &FAM = MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();
  SmallVector<Function *, 64> Funcs;

  hasBranchFusion = false;

  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    Funcs.push_back(&F);
  }

  for (Function *F : Funcs) {
    errs() << "*Running function: " << F->getName() << "\n";
    auto &DT = FAM.getResult<DominatorTreeAnalysis>(*F);
    auto &PDT = FAM.getResult<PostDominatorTreeAnalysis>(*F);
    auto &TTI = FAM.getResult<TargetIRAnalysis>(*F);
    auto &LI = FAM.getResult<LoopAnalysis>(*F);

#ifdef ENABLE_TIMING
    auto T1 = std::chrono::high_resolution_clock::now();
#endif
    runImpl(F, DT, PDT, LI, TTI);
#ifdef ENABLE_TIMING
    auto T2 = std::chrono::high_resolution_clock::now();
    auto micros =
        std::chrono::duration_cast<std::chrono::microseconds>(T2 - T1).count();
    allTime += (unsigned int)(micros);
#endif
    // ValueToValueMapTy vmap;
    // Function *F_clone = CloneFunction(F, vmap);
    // for (auto it : vmap) {
    //   it.first->dump();
    //   errs() << "-----------\n";
    //   it.second->dump();
    //   errs() << "===========\n";
    // }
    // F->replaceAllUsesWith(F_clone);
    // std::string Name = F->getName().str();
    // F->eraseFromParent();
    // F_clone->setName(Name);
    // break;
  }
  return PreservedAnalyses::none();
}

// extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
// llvmGetPassPluginInfo() {
//   return {LLVM_PLUGIN_API_VERSION, "RegionMergingPass",
//   "LLVM_VERSION_STRING",
//           [](PassBuilder &PB) {
//             PB.registerPipelineParsingCallback(
//                 [](StringRef PassName, FunctionPassManager &FPM,
//                    ArrayRef<PassBuilder::PipelineElement>) {
//                   if (PassName == "rgm") {
//                     FPM.addPass(RegionMergingPass());
//                     return true;
//                   }
//                   return false;
//                 });
//           }};
// }

extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "RegionMergingModulePass",
          "LLVM_VERSION_STRING", [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef PassName, ModulePassManager &MPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (PassName == "rgm") {
                    MPM.addPass(RegionMergingModulePass());
                    return true;
                  }
                  return false;
                });
          }};
}