add_llvm_library(LLVMMIRParser
  MILexer.cpp
  MIParser.cpp
  MIRParser.cpp

  DEPENDS
  intrinsics_gen

  LINK_COMPONENTS
    AsmParser
    CodeGen
    Core
    MC
    Support
    Target

)
