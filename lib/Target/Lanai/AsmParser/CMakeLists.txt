include_directories( ${CMAKE_CURRENT_BINARY_DIR}/.. ${CMAKE_CURRENT_SOURCE_DIR}/.. )

if(PPP)
  set(LLVM_LINK_COMPONENTS MC MCParser Support LanaiDesc LanaiInfo)
endif(PPP)
add_llvm_library(LLVMLanaiAsmParser
  LanaiAsmParser.cpp
  )

add_dependencies( LLVMLanaiAsmParser LanaiCommonTableGen )
