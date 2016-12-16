if(PPP)
  set(LLVM_LINK_COMPONENTS Support)
endif(PPP)
add_llvm_library(LLVMOption
  Arg.cpp
  ArgList.cpp
  Option.cpp
  OptTable.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Option
  )
