add_llvm_component_library(LLVMRGM
  rgm.cpp
    CFMelder/CFMelder.cpp
    CFMelder/CFMelderUtils.cpp
    CFMelder/RegionAnalyzer.cpp
    CFMelder/RegionMelder.cpp
    CFMelder/RegionReplicator.cpp
    CFMelder/FunctionMerging.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms/RGM
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms/RGM/CFMelder

  DEPENDS
  intrinsics_gen

  LINK_COMPONENTS
  Analysis
  Core
  Support
  )