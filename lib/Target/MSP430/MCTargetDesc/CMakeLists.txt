if(PPP)
  set(LLVM_LINK_COMPONENTS MC MSP430AsmPrinter MSP430Info Support)
endif(PPP)
add_llvm_library(LLVMMSP430Desc
  MSP430MCTargetDesc.cpp
  MSP430MCAsmInfo.cpp
  )
