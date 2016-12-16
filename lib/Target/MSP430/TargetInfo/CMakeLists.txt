if(PPP)
  set(LLVM_LINK_COMPONENTS Support)
endif(PPP)
add_llvm_library(LLVMMSP430Info
  MSP430TargetInfo.cpp
  )
