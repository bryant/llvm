# Ensure that each component:
# - has valid dependencies -- all deps should themselves be components,
# - do not self-depend.
# This is analogous to LLVMProjectInfo.validate_components in the old
# utils/llvm-build.
function(validate_component_deps components)
  foreach(component ${components})
    get_target_property(cdeps ${component} LINK_LIBRARIES)
    list(GET cdeps 0 first_dep)
    if(NOT ${first_dep} STREQUAL "cdeps-NOTFOUND")
      foreach(cdep ${cdeps})
        if("${cdep}" STREQUAL "${component}")
          message(SEND_ERROR "${component} cannot depend on itself.")
        elseif(cdep MATCHES "^LLVM")
          list(FIND components ${cdep} idx)
          if(${idx} EQUAL -1)
            message(SEND_ERROR "${component} depends on ${cdep}, which cannot be found.")
          endif()
        endif("${cdep}" STREQUAL "${component}")
      endforeach()
    endif()
  endforeach(component)
endfunction(validate_component_deps)
