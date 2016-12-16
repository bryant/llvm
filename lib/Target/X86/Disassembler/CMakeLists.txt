if(PPP)
  set(LLVM_LINK_COMPONENTS MCDisassembler Support X86Info)
endif(PPP)
add_llvm_library(LLVMX86Disassembler
  X86Disassembler.cpp
  X86DisassemblerDecoder.cpp
  )
