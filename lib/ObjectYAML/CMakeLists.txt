add_llvm_library(LLVMObjectYAML
  YAML.cpp
  COFFYAML.cpp
  ELFYAML.cpp
  MachOYAML.cpp
  ObjectYAML.cpp
  DWARFYAML.cpp

  LINK_COMPONENTS
    Support
)
