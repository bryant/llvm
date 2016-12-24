if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC MCDisassembler Object Support X86AsmPrinter X86Info)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMX86Desc
  X86AsmBackend.cpp
  X86MCTargetDesc.cpp
  X86MCAsmInfo.cpp
  X86MCCodeEmitter.cpp
  X86MachObjectWriter.cpp
  X86ELFObjectWriter.cpp
  X86WinCOFFStreamer.cpp
  X86WinCOFFObjectWriter.cpp
  )
