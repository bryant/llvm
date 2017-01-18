include_directories( ${CMAKE_CURRENT_BINARY_DIR}/..
                     ${CMAKE_CURRENT_SOURCE_DIR}/.. )

add_llvm_library(LLVMAVRAsmPrinter
  AVRInstPrinter.cpp

  LINK_COMPONENTS
    MC
    Support

)

add_dependencies(LLVMAVRAsmPrinter AVRCommonTableGen)