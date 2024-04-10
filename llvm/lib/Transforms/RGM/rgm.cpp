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

#define DEBUG_TYPE "rgm"
STATISTIC(profitableRegions, "The # of profitable region pairs");

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

  RegionTree(Region *region) : region(region), matchId(-1), level(0) {
    for (auto it : region->blocks()) {
      blocks.push_back(it);
    }
    if (auto r = region->getExit()) {
      blocks.push_back(r);
    }
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
      if (R->isSimple())
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

static void ComputeSARegionMatch(SmallVectorImpl<Region *> &LeftRegions,
                                 SmallVectorImpl<Region *> &RightRegions) {
  RegionMeldingProfitabilityModel ScoringFunc;
  auto SMSA =
      SmithWaterman<Region *, SmallVectorImpl<Region *>, nullptr>(ScoringFunc);

  auto Result = SMSA.compute(LeftRegions, RightRegions);
  int AlignedReginPairs = 0;
  for (auto Entry : Result) {
    Region *L = Entry.getLeft();
    Region *R = Entry.getRight();
    if (Entry.match()) {
      RegionComparator RC(L, R);
      bool Check = RC.compare();
      assert(Check && "Aligned regions are not similar!");
      std::shared_ptr<MergeableRegionPair> RegionPair =
          std::make_shared<MergeableRegionPair>(*L, *R, RC);

      // BestRegionMatch.push_back(RegionPair);
      AlignedReginPairs++;
      L->dump();
      errs() << "--------------\n";
      R->dump();
      errs() << "==============\n";
    }
  }

  errs() << "Number of aligned region pairs : " << AlignedReginPairs << "\n";
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
          if (it->getRegion()->isSimple())
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

static AllocaInst *MemfyInst(Function &F, std::set<Instruction *> &InstSet) {
  BasicBlock *PreBB = &(F.getEntryBlock());
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

static bool commitChanges(Function &F) {

#ifdef TIME_STEPS_DEBUG
  TimeCodeGenFix.startTimer();
#endif

  Function *MergedFunc = &F;

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

static void runImpl(Function &F, DominatorTree &DT, PostDominatorTree &PDT,
                    LoopInfo &LI, TargetTransformInfo &TTI) {

  // runAnalysisOnly(F, DT, PDT, LI, TTI);
  std::vector<RegionTree *> regions;

  runRegionMatch(F, DT, PDT, LI, TTI, regions);
  // melding(F, DT, PDT, LI, TTI);
  std::vector<Match> matches;
  findSimilarRegion(regions, matches);

  auto cmp = [](const Match &v1, const Match &v2) {
    if (v1.level == v2.level) {
      return v1.similarityScores > v2.similarityScores;
    } else {
      return v1.level > v2.level;
    }
  };

  std::sort(matches.begin(), matches.end(), cmp);
  int i = 0;
  std::unordered_set<BasicBlock *> ProcessedBBs;
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

  for (auto &match : matches) {
    // if (i++ != 12)
    //   continue;
    auto it = match.match;
    Region *RegionL = it.first->getRegion();
    Region *RegionR = it.second->getRegion();

    bool Processed = false;
    for (auto i : it.first->getBlocks()) {
      if (ProcessedBBs.find(i) != ProcessedBBs.end()) {
        Processed = true;
        break;
      }
    }
    for (auto i : it.second->getBlocks()) {
      if (ProcessedBBs.find(i) != ProcessedBBs.end()) {
        Processed = true;
        break;
      }
    }

    if (Processed)
      continue;

    if (RegionL->getEntry() == RegionR->getExit() ||
        RegionL->getExit() == RegionR->getEntry()) {
      continue;
    }

    // if (!RegionL->isSimple()) {
    //   continue;
    // }
    // if (!RegionR->isSimple()) {
    //   continue;
    // }

    RegionL->dump();
    errs() << "------------\n";
    RegionR->dump();
    errs() << "============\n";

    RegionComparator RC(RegionL, RegionR);
    RC.compare();
    std::shared_ptr<MergeableRegionPair> regionPair =
        std::make_shared<MergeableRegionPair>(*RegionL, *RegionR, RC);
    // errs() << "Regions are similar\n";
    //   errs() << *regionPair << "\n";
    //   errs() << "Similarity score is " << regionPair->getSimilarityScore()
    //         << "\n";
    if (regionPair->getSimilarityScore() < 0.3)
      continue;

    SESERegion LeftR(RegionL);
    SESERegion RightR(RegionR);

    int SizeLeft = 0;
    int SizeRight = 0;

    TargetTransformInfo TTI(F.getParent()->getDataLayout());

    std::set<BasicBlock *> KnownBBs;
    for (BasicBlock &BB : LeftR) {
      KnownBBs.insert(&BB);

      for (Instruction &I : BB) {
        auto cost = TTI.getInstructionCost(
            &I, TargetTransformInfo::TargetCostKind::TCK_CodeSize);
        SizeLeft += cost.getValue().value();
      }
    }
    for (BasicBlock &BB : RightR) {
      KnownBBs.insert(&BB);

      for (Instruction &I : BB) {
        auto cost = TTI.getInstructionCost(
            &I, TargetTransformInfo::TargetCostKind::TCK_CodeSize);
        SizeRight += cost.getValue().value();
      }
    }

    bool UseCostInFingerprint = true;
    AlignmentStats TotalAlignmentStats;
    AlignedSequence<Value *> AlignedInsts =
        FunctionMerger::alignBlocks(LeftR, RightR, TotalAlignmentStats,
                                    (UseCostInFingerprint ? (&TTI) : nullptr));

    for (auto &Entry : AlignedInsts) {

      if (true) {
        errs() << "-----------------------------------------------------\n";
        if (Entry.get(0)) {
          if (isa<BasicBlock>(Entry.get(0)))
            errs() << Entry.get(0)->getName() << "\n";
          else
            Entry.get(0)->dump();
        } else
          errs() << "\t-\n";
        if (Entry.get(1)) {
          if (isa<BasicBlock>(Entry.get(1)))
            errs() << Entry.get(1)->getName() << "\n";
          else
            Entry.get(1)->dump();
        } else {
          errs() << "\t-\n";
        }
      }
    }

    LLVMContext &Context = F.getContext();
    const DataLayout *DL = &F.getParent()->getDataLayout();
    Type *IntPtrTy = DL->getIntPtrType(Context);

    ValueToValueMapTy VMap;
    // initialize VMap
    for (Argument &Arg : F.args()) {
      VMap[&Arg] = &Arg;
    }

    for (BasicBlock &BB : F) {
      if (KnownBBs.count(&BB))
        continue;
      VMap[&BB] = &BB;
      for (Instruction &I : BB) {
        VMap[&I] = &I;
      }
    }

    FunctionMergingOptions Options = FunctionMergingOptions()
                                         .enableUnifiedReturnTypes(false)
                                         .matchOnlyIdenticalTypes(true);

    BasicBlock *EntryBB = BasicBlock::Create(Context, "rgmEntry", &F);
    BasicBlock *LBB = RegionL->getEntry();
    BasicBlock *RBB = RegionR->getEntry();
    IRBuilder<> builder(EntryBB);
    PHINode *labelPhiNode =
        builder.CreatePHI(Type::getInt1Ty(F.getContext()), 2);
    labelPhiNode->addIncoming(ConstantInt::get(Type::getInt1Ty(Context), 1),
                              LBB);
    labelPhiNode->addIncoming(ConstantInt::get(Type::getInt1Ty(Context), 0),
                              RBB);
    FunctionMerger::SALSSACodeGen CG(LeftR.Blocks, RightR.Blocks);
    CG.insert(labelPhiNode);
    CG.setFunctionIdentifier(labelPhiNode)
        .setEntryPoints(LBB, RBB)
        .setReturnTypes(F.getReturnType(), F.getReturnType())
        .setMergedFunction(&F)
        .setMergedEntryPoint(EntryBB)
        .setMergedReturnType(F.getReturnType(), false)
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
      continue;
    }

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

          // Same block can be a predecessor multiple times and can have
          // multiple incoming edges into BB To keep BB's predecessor
          // information consistent with the phi incoming values, we need to
          // keep track of the number of incoming edges from each predecessor
          // block
          // std::map<BasicBlock *, std::map<BasicBlock *, Value *>>
          // NewEntries;
          std::map<BasicBlock *,
                   std::map<BasicBlock *, std::pair<Value *, int>>>
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
              // simply copy incoming values from outside the two regions
              // being merged
              NewPHI->addIncoming(PHI->getIncomingValue(i),
                                  PHI->getIncomingBlock(i));
            }
          }

          if (Debug) {
            errs() << "Num entries: " << NewEntries.size() << "\n";
            for (auto &Pair : NewEntries) {
              errs() << "Incoming Block: " << Pair.first->getName().str()
                     << "\n";
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
              errs() << "Incoming Block: " << Pair.first->getName().str()
                     << "\n";
            }
            if (Pair.second.size() == 1) {
              auto &InnerPair = *(Pair.second.begin());
              Value *V = InnerPair.second.first;
              int repeats = InnerPair.second.second;
              for (int i = 0; i < repeats; ++i)
                NewPHI->addIncoming(V, Pair.first);
            } else if (Pair.second.size() == 2) {
              /*
              Values that were originally coming from different basic blocks
              that have been merged must be properly handled. In this case, we
              add a selection in the merged incomming block to produce the
              correct value for the phi node.
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
                  // TODO: handle if one of the values is the terminator
                  // itself!
                  MergedV = Builder.CreateSelect(labelPhiNode, LeftV, RightV);
                  if (SelectInst *SelI = dyn_cast<SelectInst>(MergedV))
                    CG.insert(SelI);
                }
                for (int i = 0; i < repeats; ++i)
                  NewPHI->addIncoming(MergedV, Pair.first);
              } else {
                errs()
                    << "ERROR: THIS IS WEIRD! MAYBE IT SHOULD NOT BE HERE!\n";
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
    errs() << Error << '\n';

    if (Debug) {
      errs() << "Modified function\n";
    }

    int MergedSize = 0;
    if (Debug) {
      errs() << "Computing size...\n";
    }
    for (Instruction *I : CG) {
      auto cost = TTI.getInstructionCost(
          I, TargetTransformInfo::TargetCostKind::TCK_CodeSize);
      MergedSize += cost.getValue().value();
    }

    if (Debug) {
      errs() << "SizeLeft: " << SizeLeft << "\n";
      errs() << "SizeRight: " << SizeRight << "\n";
      errs() << "Original Size: " << (SizeLeft + SizeRight) << "\n";
      errs() << "New Size: " << MergedSize << "\n";
    }

    errs() << "SizeDiff: " << (SizeLeft + SizeRight) << " X " << MergedSize
           << " : " << ((int)(SizeLeft + SizeRight) - ((int)MergedSize))
           << " : ";

    bool Profitable = MergedSize < SizeLeft + SizeRight;

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

      continue;
    }

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

    for (BasicBlock *BB : it.first->getBlocks()) {
      ProcessedBBs.insert(BB);
    }
    for (BasicBlock *BB : it.second->getBlocks()) {
      ProcessedBBs.insert(BB);
    }

    builder.SetInsertPoint(LBB);
    Instruction *NewBrL = builder.CreateBr(EntryBB);
    builder.SetInsertPoint(RBB);
    Instruction *NewBrR = builder.CreateBr(EntryBB);

    if (Debug) {
      errs() << "After deleting the old code\n";
      // F.dump();
    }
    if (!commitChanges(F)) {
      // F.dump();
      errs() << "ERROR: committing final changes to the fused branches "
                "!!!!!!!\n";
    }
    if (Debug) {
      errs() << "Final version\n";
      // F.dump();
    }
    // break;
    DT.recalculate(F);
    PDT.recalculate(F);
  }
  SimplifyCFGOptions SimplifyCFGOptionsObj;
  FunctionPassManager FPM;
  if (simplifyFunction(F, TTI,
                       SimplifyCFGOptionsObj.setSimplifyCondBranch(false)
                           .sinkCommonInsts(false)
                           .hoistCommonInsts(false))) {
    DT.recalculate(F);
    PDT.recalculate(F);
  }
}

PreservedAnalyses RegionMergingPass::run(Function &F,
                                         FunctionAnalysisManager &FAM) {
  errs() << "Running function: " << F.getName() << "\n";

  auto &DT = FAM.getResult<DominatorTreeAnalysis>(F);
  auto &PDT = FAM.getResult<PostDominatorTreeAnalysis>(F);
  auto &TTI = FAM.getResult<TargetIRAnalysis>(F);
  auto &LI = FAM.getResult<LoopAnalysis>(F);

  runImpl(F, DT, PDT, LI, TTI);

  return PreservedAnalyses::none();
}

PreservedAnalyses RegionMergingModulePass::run(Module &M,
                                                 ModuleAnalysisManager &MAM) {
  auto &FAM = MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();
  SmallVector<Function *, 64> Funcs;

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
    runImpl(*F, DT, PDT, LI, TTI);
  }
  return PreservedAnalyses::none();
}

extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "RegionMergingPass", "LLVM_VERSION_STRING",
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef PassName, FunctionPassManager &FPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (PassName == "rgm") {
                    FPM.addPass(RegionMergingPass());
                    return true;
                  }
                  return false;
                });
          }};
}
