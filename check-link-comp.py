import os
import re
import sys
import difflib
sys.path.append("./utils/llvm-build")
from llvmbuild.main import LLVMProjectInfo as LB

def get_link_comps(comp):
    #import pudb; pudb.set_trace()
    s = comp_cmake(comp)
    m = re.search(r"set\(\s*LLVM_LINK_COMPONENTS\s+([^\)]+?)\)", s, re.DOTALL)
    return [] if m is None \
              else sorted(m.group(1)
                           .replace("${LLVM_TARGETS_TO_BUILD}", "all-targets")
                           .split())

def comp_cmake_path(comp):
    subdir = os.path.dirname(comp._source_path)
    return os.path.join(subdir, "CMakeLists.txt")

def comp_cmake(comp):
    try:
        return open(comp_cmake_path(comp)).read()
    except IOError:
        return ""

class ThisAintALib(Exception): pass

def copy_lb_deps(comp):
    raw = comp_cmake(comp)
    m = re.findall(r"^add_llvm_(?:library|target)\([^\)]+\)", raw,
                   flags=re.DOTALL | re.MULTILINE)
    if len(m) != 1 or "LINK_COMPONENTS" in raw:
        #raise ThisAintALib
        return None

    # for target comps, the deps are found in target_name + "CodeGen"
    if m[0].startswith("add_llvm_target") and not comp.name.endswith("CodeGen"):
        comp = libs[comp.name + "CodeGen"]

    def subit(m):
        deps = "\n".join(" " * 4 + libnames.get(dep, "WTF")
                         for dep in comp.required_libraries)
        return m.group(0).rstrip() + "\n\n  LINK_COMPONENTS\n" + deps + "\n\n"
    return re.sub(r"^add_llvm_(library|target)\(([^\)]+)", subit, raw, count=1,
                  flags=re.DOTALL | re.MULTILINE)

#for x in load_infos_from_path("."):
libs = {lib.name: lib for lib in LB.load_infos_from_path(".")}

# e.g., Scalar => ScalarOpts
libnames = {lib.name : getattr(lib, "library_name", lib.name) or lib.name
            for lib in libs.itervalues()}

complibs = filter(lambda c: c._source_path.startswith("./lib"),
                  libs.itervalues())

newcmakes = {c.name: copy_lb_deps(c) for c in complibs}

def showme():
    diff = difflib.ndiff
    rv = ""
    for i, c in enumerate(libs.itervalues()):
        if hasattr(c, "required_libraries"):
            lb = sorted(c.required_libraries)
            cm = sorted(get_link_comps(c))
            d = "\n".join(diff(cm, lb))
            rv += "%d %s %s\n%s\n\n" % (i, c.name, c._source_path, d)
    return rv

if __name__=='__main__':
    pass  # print(showme())
