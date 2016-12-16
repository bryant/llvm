set(LLVM_TARGET_DEFINITIONS Options.td)
tablegen(LLVM Options.inc -gen-opt-parser-defs)
add_public_tablegen_target(LibOptionsTableGen)

if(PPP)
  set(LLVM_LINK_COMPONENTS Object Option Support)
endif(PPP)
add_llvm_library(LLVMLibDriver
  LibDriver.cpp
  )
add_dependencies(LLVMLibDriver LibOptionsTableGen)
