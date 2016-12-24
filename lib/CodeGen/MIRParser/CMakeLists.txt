if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS AsmParser CodeGen Core MC Support Target)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMMIRParser
  MILexer.cpp
  MIParser.cpp
  MIRParser.cpp

  DEPENDS
  intrinsics_gen
  )
