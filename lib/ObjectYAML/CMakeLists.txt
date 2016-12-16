if(PPP)
  set(LLVM_LINK_COMPONENTS Support)
endif(PPP)
add_llvm_library(LLVMObjectYAML
  YAML.cpp
  COFFYAML.cpp
  ELFYAML.cpp
  MachOYAML.cpp
  ObjectYAML.cpp
  DWARFYAML.cpp
  )
