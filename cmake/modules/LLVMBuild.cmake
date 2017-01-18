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

# Generates LibraryDependencies.inc, needed by tools/llvm-config.
function(gen_libdep_inc components targets noninstalls)
  # Handle actual libs and track leaf comps for the "all" pseudo
  set(leaf_comps "${components}")
  list(FILTER leaf_comps INCLUDE REGEX "^LLVM")
  foreach(component ${components})
    if(component MATCHES "^LLVM")
      get_target_property(cdeps ${component} LINK_LIBRARIES)
      list(FILTER cdeps INCLUDE REGEX "^LLVM")

      set(cdepz "")
      foreach(cdep ${cdeps})
        # leaf components are the ones that nobody else depends on.
        list(REMOVE_ITEM leaf_comps "${cdep}")
        lib_to_complower(cdep "${cdep}")
        set(cdepz "${cdepz}" "${cdep}")
      endforeach()

      lib_to_complower(complowered "${component}")
      gen_libdep_entry(entry "${complowered}" "${component}" 1 "${cdepz}")
      set(entries "${entries}" "${entry}")
    endif(component MATCHES "^LLVM")
  endforeach(component)

  # Handle targets, i.e., {"x86", nullptr, true, {...}}, also "all-targets"
  set(all_targets_ "")
  foreach(target ${targets})
    set(cdepz "")
    # Lanai uses InstPrinter rather than AsmPrinter
    foreach(targcomp AsmParser AsmPrinter CodeGen Desc Disassembler Info InstPrinter Utils)
      list(FIND components "LLVM${target}${targcomp}" idx)
      if(NOT ${idx} EQUAL -1)
        list(REMOVE_ITEM leaf_comps "LLVM${target}${targcomp}")
        string(TOLOWER "${target}${targcomp}" cdep)
        set(cdepz "${cdepz}" "${cdep}")
      endif()
    endforeach()
    string(TOLOWER "${target}" target)
    # all-targets
    set(all_targets_ "${all_targets_}" "${target}")
    gen_libdep_entry(entry "${target}" "" 1 "${cdepz}")
    set(entries "${entries}" "${entry}")
  endforeach()

  # Handle "native," "nativecodegen," and "engine" pseudos
  list(FIND targets "${LLVM_NATIVE_ARCH}" have_native_backend)
  list(FIND LLVM_TARGETS_WITH_JIT "${LLVM_NATIVE_ARCH}" have_jit)
  #         ^ FIXME: leaky abstraction.
  if(NOT have_native_backend EQUAL -1)
    # native backend will be built
    string(TOLOWER "${LLVM_NATIVE_ARCH}" native_)
    gen_libdep_entry(entry "native" "" 1 "${native_}")
    set(entries "${entries}" "${entry}")
    gen_libdep_entry(entry "nativecodegen" "" 1 "${native_}codegen")
    set(entries "${entries}" "${entry}")
    if (NOT have_jit EQUAL -1)
      gen_libdep_entry(entry "engine" "" 1 "mcjit;native")
      set(entries "${entries}" "${entry}")
    endif()
  else()
    gen_libdep_entry(entry "native" "" 1 "")
    set(entries "${entries}" "${entry}")
    gen_libdep_entry(entry "nativecodegen" "" 1 "")
    set(entries "${entries}" "${entry}")
    gen_libdep_entry(entry "engine" "" 1 interpreter)
    set(entries "${entries}" "${entry}")
  endif()

  # Handle "all"
  set(cdepz "all-targets;nativecodegen;engine")
  foreach(leaf ${leaf_comps})
    lib_to_complower(leaf "${leaf}")
    set(cdepz "${cdepz}" "${leaf}")
  endforeach()
  gen_libdep_entry(entry "all" "" 1 "${cdepz}")
  set(entries "${entries}" "${entry}")

  # Handle "all-targets"
  gen_libdep_entry(entry "all-targets" "" 1 "${all_targets_}")
  set(entries "${entries}" "${entry}")

  # TODO: handle non-build-tree comps, like gtest and gtest_main

  list(SORT entries)
  join_list(LLVM_COMPONENTS ",\n" "${entries}")
  list(LENGTH entries LLVM_COMPONENT_COUNT)
  configure_file(
    ${CMAKE_SOURCE_DIR}/tools/llvm-config/LibraryDependencies.inc.in
    ${CMAKE_BINARY_DIR}/tools/llvm-config/LibraryDependencies.inc
    @ONLY
  )
endfunction(gen_libdep_inc)

# LLVMSomeLib => somelib
function(lib_to_complower rv libname)
  string(REGEX REPLACE "^LLVM" "" libname "${libname}")
  string(TOLOWER "${libname}" libname)
  set(${rv} "${libname}" PARENT_SCOPE)
endfunction(lib_to_complower)

function(gen_libdep_entry output name_ lib_ is_installed required_libs)
  if(lib_ STREQUAL "")
    set(lib_ "nullptr")
  else()
    set(lib_ "\"${lib_}\"")
  endif()

  if(is_installed)
    set(is_installed "true")
  else()
    set(is_installed "false")
  endif()

  list(SORT required_libs)
  join_quoted(reqs "${required_libs}")

  string(CONFIGURE "{\"@name_@\", @lib_@, @is_installed@, {@reqs@}}" retval @ONLY)
  set(${output} "${retval}" PARENT_SCOPE)
endfunction(gen_libdep_entry)

# this is cmake.
function(join_list rv delim list_)
  foreach(j ${list_})
    string(CONFIGURE "@j@" jjj @ONLY)
    set(rv_ "${rv_}${delim}${jjj}")
  endforeach()
  string(REGEX REPLACE "^${delim}" "" rv__ "${rv_}")
  set(${rv} "${rv__}" PARENT_SCOPE)
endfunction(join_list)

function(join_quoted rv list_)
  foreach(j ${list_})
    string(CONFIGURE "@j@" jjj @ONLY ESCAPE_QUOTES)
    set(rv_ "${rv_}, \"${jjj}\"")
  endforeach()
  string(REGEX REPLACE "^, " "" rv__ "${rv_}")
  set(${rv} "${rv__}" PARENT_SCOPE)
endfunction(join_quoted)

# vim: set syntax=cmake textwidth=0 tabstop=2 shiftwidth=2:
