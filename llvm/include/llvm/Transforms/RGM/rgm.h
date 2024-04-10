#ifndef LLVM_TRANSFORMS_RGM_RGM_H
#define LLVM_TRANSFORMS_RGM_RGM_H

#include "llvm/IR/PassManager.h"

namespace llvm {

class RegionMergingPass : public PassInfoMixin<RegionMergingPass> {
public:
    PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM);
};

class RegionMergingModulePass : public PassInfoMixin<RegionMergingModulePass> {
public:
    PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM);
};

} // namespece llvm

#endif // LLVM_TRANSFORMS_RGM_RGM_H