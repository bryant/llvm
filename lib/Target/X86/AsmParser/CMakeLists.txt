if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC MCParser Support X86Desc X86Info)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMX86AsmParser
  X86AsmInstrumentation.cpp
  X86AsmParser.cpp
  )
