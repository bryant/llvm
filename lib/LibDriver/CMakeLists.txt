set(LLVM_TARGET_DEFINITIONS Options.td)
tablegen(LLVM Options.inc -gen-opt-parser-defs)
add_public_tablegen_target(LibOptionsTableGen)

if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS Object Option Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMLibDriver
  LibDriver.cpp
  )
add_dependencies(LLVMLibDriver LibOptionsTableGen)
