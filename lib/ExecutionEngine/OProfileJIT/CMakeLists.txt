
include_directories( ${LLVM_OPROFILE_DIR} ${CMAKE_CURRENT_SOURCE_DIR}/.. )

if(PPP)
  set(LLVM_LINK_COMPONENTS Support Object ExecutionEngine)
endif(PPP)
add_llvm_library(LLVMOProfileJIT
  OProfileJITEventListener.cpp
  OProfileWrapper.cpp
  )
