if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC Object Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMRuntimeDyld
  JITSymbol.cpp
  RTDyldMemoryManager.cpp
  RuntimeDyld.cpp
  RuntimeDyldChecker.cpp
  RuntimeDyldCOFF.cpp
  RuntimeDyldELF.cpp
  RuntimeDyldMachO.cpp
  Targets/RuntimeDyldELFMips.cpp

  DEPENDS
  intrinsics_gen
  )
