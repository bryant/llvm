if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC MCParser Support SystemZDesc SystemZInfo)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMSystemZAsmParser
  SystemZAsmParser.cpp
  )
