cmake_minimum_required(VERSION 3.5)
set(PROJECT_NAME peirce)


set(LIBRARY_LIST 
    clangAST  clangASTMatchers  clangAnalysis clangBasic  clangDriver clangEdit clangFrontend clangFrontendTool clangLex  clangParse  clangSema clangEdit clangRewrite  clangRewriteFrontend  clangStaticAnalyzerFrontend clangStaticAnalyzerCheckers clangStaticAnalyzerCore clangCrossTU  clangIndex  clangSerialization  clangToolingCore  clangTooling  clangFormat
    )


# below is the list of names of the llvm libs
#set(COMPONENT_LIST aarch64 aarch64asmparser aarch64asmprinter aarch64codegen aarch64desc aarch64disassembler aarch64info aarch64utils amdgpu amdgpuasmparser amdgpuasmprinter amdgpucodegen amdgpudesc amdgpudisassembler amdgpuinfo amdgpuutils analysis arm armasmparser armasmprinter armcodegen armdesc armdisassembler arminfo asmparser asmprinter binaryformat bitreader bitwriter bpf bpfasmparser bpfasmprinter bpfcodegen bpfdesc bpfdisassembler bpfinfo codegen core coroutines coverage debuginfocodeview debuginfodwarf debuginfomsf debuginfopdb demangle dlltooldriver engine executionengine fuzzmutate globalisel gtest gtest_main hexagon hexagonasmparser hexagoncodegen hexagondesc hexagondisassembler hexagoninfo instcombine instrumentation interpreter ipo irreader lanai lanaiasmparser lanaiasmprinter lanaicodegen lanaidesc lanaidisassembler lanaiinfo libdriver lineeditor linker lto mc mca mcdisassembler mcjit mcparser mips mipsasmparser mipsasmprinter mipscodegen mipsdesc mipsdisassembler mipsinfo mirparser msp430 msp430asmparser msp430asmprinter msp430codegen msp430desc msp430disassembler msp430info native nativecodegen nvptx nvptxasmprinter nvptxcodegen nvptxdesc nvptxinfo objcarcopts object objectyaml option optremarks orcjit passes powerpc powerpcasmparser powerpcasmprinter powerpccodegen powerpcdesc powerpcdisassembler powerpcinfo profiledata runtimedyld scalaropts selectiondag sparc sparcasmparser sparcasmprinter sparccodegen sparcdesc sparcdisassembler sparcinfo support symbolize systemz systemzasmparser systemzasmprinter systemzcodegen systemzdesc systemzdisassembler systemzinfo tablegen target testingsupport textapi transformutils vectorize webassembly webassemblyasmparser webassemblyasmprinter webassemblycodegen webassemblydesc webassemblydisassembler webassemblyinfo windowsmanifest x86 x86asmparser x86asmprinter x86codegen x86desc x86disassembler x86info x86utils xcore xcoreasmprinter xcorecodegen xcoredesc xcoredisassembler xcoreinfo xray)

# x86asmparser   x86desc   x86asmprinter   x86info   x86utils
set(COMPONENT_LIST  x86asmparser   x86desc   x86asmprinter   x86info   x86utils  ipo  scalaropts  instcombine  transformutils  analysis  target  option   mcparser   mc   object   bitreader   core   support)

find_package(LLVM REQUIRED CONFIG)
message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")  

#set(LLVM_ENABLE_ZLIB OFF)

# add local customized dependencies.

add_library(Bridge STATIC 
  Bridge.cpp
  Bridge.h  
)

add_library(Checker STATIC 
  Checker.cpp
  Checker.h 
)

add_library(CodeCoordinate STATIC 
  CodeCoordinate.cpp
  CodeCoordinate.h  
)

add_library(Identifier STATIC 
  Identifier.cpp
  Identifier.h  
)

add_library(Interpretation STATIC 
  Interpretation.cpp
  Interpretation.h  
)

add_library(Literal STATIC 
  Literal.cpp
  Literal.h 
)

add_library(OpAddExpression STATIC 
  OpAddExpression.cpp
  OpAddExpression.h 
)

add_library(Oracle STATIC 
  Oracle.cpp
  Oracle.h  
)

add_library(VariableExpression STATIC 
  VariableExpression.cpp
  VariableExpression.h  
)

include_directories("/llvm/tools/clang/include")

include_directories("/llvm/build/bin")

include_directories("/llvm/build/tools/clang/include/")

include_directories("/llvm/include")

include_directories("/llvm/build/include/")

include_directories(/llvm/build/lib)

link_directories(/llvm/build/lib)


add_definitions(
-D__STDC_LIMIT_MACROS
-D__STDC_CONSTANT_MACROS
)

add_executable(${PROJECT_NAME} main.cpp)

if ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
  foreach(link_lib IN LISTS LIBRARY_LIST)
    target_link_libraries(${PROJECT_NAME} optimized ${link_lib})
    target_link_libraries(${PROJECT_NAME} debug     ${link_lib}d)
  endforeach()
else()
  target_link_libraries(${PROJECT_NAME} ${LIBRARY_LIST})
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11 -Wno-unused-parameter -fno-strict-aliasing -fno-rtti -fno-exceptions -O0 -g -Wall")
endif()

llvm_map_components_to_libnames(llvm_libs ${COMPONENT_LIST})
target_link_libraries(${PROJECT_NAME} ${llvm_libs})


# not working yet ....
#set(LLVM_BIN_PATH /llvm/build/bin/)
#set(LLVM_LDFLAGS "`$(LLVM_BIN_PATH)/llvm-config --ldflags --libs --system-libs`")
#target_link_libraries(${PROJECT_NAME} ${LLVM_LDFLAGS})


target_link_libraries(${PROJECT_NAME}
  LLVMX86AsmParser # MC, MCParser, Support, X86Desc, X86Info
  LLVMX86Desc # MC, Support, X86AsmPrinter, X86Info
  LLVMX86AsmPrinter # MC, Support, X86Utils
  LLVMX86Info # MC, Support, Target
  LLVMX86Utils # Core, Support
  LLVMipo
  LLVMScalarOpts
  LLVMInstCombine
  LLVMTransformUtils
  LLVMipa
  LLVMAnalysis
  LLVMTarget
  LLVMOption # Support
  LLVMMCParser # MC, Support
  LLVMMC # Object, Support
  LLVMObject # BitReader, Core, Support
  LLVMBitReader # Core, Support
  LLVMCore # Support
  LLVMSupport
)

target_link_libraries(${PROJECT_NAME}
    Bridge
    Checker
    CodeCoordinate
    Identifier
    Interpretation
    Literal
    OpAddExpression
    Oracle
    VariableExpression
)