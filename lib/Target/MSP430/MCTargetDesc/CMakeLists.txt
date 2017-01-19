add_llvm_library(LLVMMSP430Desc
  MSP430MCTargetDesc.cpp
  MSP430MCAsmInfo.cpp

  LINK_COMPONENTS
    MC
    MSP430AsmPrinter
    MSP430Info
    Support
)
