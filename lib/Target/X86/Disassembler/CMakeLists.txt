if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MCDisassembler Support X86Info)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMX86Disassembler
  X86Disassembler.cpp
  X86DisassemblerDecoder.cpp
  )
