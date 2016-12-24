if(HAVE_LIBEDIT)
  set(link_libs edit)
endif()

if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMLineEditor
  LineEditor.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/LineEditor

  LINK_LIBS
  ${link_libs}
  )
