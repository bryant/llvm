include_directories( ${CMAKE_CURRENT_BINARY_DIR}/.. ${CMAKE_CURRENT_SOURCE_DIR}/.. )

if(PPP)
  set(LLVM_LINK_COMPONENTS Support)
endif(PPP)
add_llvm_library(LLVMWebAssemblyInfo
  WebAssemblyTargetInfo.cpp
  )

add_dependencies(LLVMWebAssemblyInfo WebAssemblyCommonTableGen)
