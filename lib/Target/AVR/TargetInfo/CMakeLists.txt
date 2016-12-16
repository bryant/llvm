include_directories( ${CMAKE_CURRENT_BINARY_DIR}/..
                     ${CMAKE_CURRENT_SOURCE_DIR}/.. )

if(PPP)
  set(LLVM_LINK_COMPONENTS MC Support)
endif(PPP)
add_llvm_library(LLVMAVRInfo
  AVRTargetInfo.cpp
)

add_dependencies(LLVMAVRInfo AVRCommonTableGen)

