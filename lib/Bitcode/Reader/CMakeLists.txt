if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS Core Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMBitReader
  BitReader.cpp
  BitcodeReader.cpp
  BitstreamReader.cpp
  MetadataLoader.cpp
  ValueList.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Bitcode

  DEPENDS
  intrinsics_gen
  )
