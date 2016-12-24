
include_directories( ${LLVM_OPROFILE_DIR} ${CMAKE_CURRENT_SOURCE_DIR}/.. )

if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS Support Object ExecutionEngine)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMOProfileJIT
  OProfileJITEventListener.cpp
  OProfileWrapper.cpp
  )
