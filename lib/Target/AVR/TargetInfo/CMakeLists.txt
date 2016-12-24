include_directories( ${CMAKE_CURRENT_BINARY_DIR}/..
                     ${CMAKE_CURRENT_SOURCE_DIR}/.. )

if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMAVRInfo
  AVRTargetInfo.cpp
)

add_dependencies(LLVMAVRInfo AVRCommonTableGen)

