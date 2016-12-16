if(HAVE_LIBEDIT)
  set(link_libs edit)
endif()

if(PPP)
  set(LLVM_LINK_COMPONENTS Support)
endif(PPP)
add_llvm_library(LLVMLineEditor
  LineEditor.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/LineEditor

  LINK_LIBS
  LLVMSupport
  ${link_libs}
  )
