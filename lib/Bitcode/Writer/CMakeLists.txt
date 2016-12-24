if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS Analysis Core Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMBitWriter
  BitWriter.cpp
  BitcodeWriter.cpp
  BitcodeWriterPass.cpp
  ValueEnumerator.cpp

  DEPENDS
  intrinsics_gen
  )
