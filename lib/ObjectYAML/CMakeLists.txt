if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMObjectYAML
  YAML.cpp
  COFFYAML.cpp
  ELFYAML.cpp
  MachOYAML.cpp
  ObjectYAML.cpp
  DWARFYAML.cpp
  )
