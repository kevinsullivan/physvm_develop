TODO:


Hannah's Todo

* Improve matchers for correctness in general
    - Match Vector class by name
    - Match Vector::vec_add only within class Vector
    - Match Vector instances by type
    - Match calls only to *Vector::* vec_add
 * get the name, file, line no. of each vector instance
* bind the parameters of vec_add expression
* add interpretation for expression
* generate lean file for analysis
* make oracle ask about declarations by name, file, line number
* fix dockerfile to install Lean and its math libraries, e.g., using elan
* fix oracle so that it does what it says it's doing: return selected space
* fix makefile: use cmake and ninja
* add "apt-get install libboost-all-dev -y" to dockerfile
* add installing emacs to dockerfile
* configure LLVM to build with RTTI
  - set(LLVM_REQUIRES_RTTI 1) in CMakeLists.txt
  - should also enable exception handling in compiler
  - See https://caesr.uwaterloo.ca/misc/boost-llvm-clang.html
  - put "apt-get install -y gdb" in docker file
  - have docker file add /usr/lib/llvm-3.9/bin/ to PATH (for clang-query)
  - to docker file add code 'ln -s /llvm/build/lib ./lib' in ./peirce
* add "apt-get update" to docker setup commands
DONE:

~~*Do the same stuff for expressions that we just did for vector instances.~~

~~*Implement domain.isConsistent. This means iterating over the domain objects and writing out a corresponding Lean file and sending it off to the type checker.~~

~~*Connect "ASTNode" object to the Clang AST node objects that you're
finding in the code.~~

~~*Update the oracle so that it asks you about which spaces vectors belong to.~~

~~*Update readme file.~~

~~*Update .gitignore so that we don't push binaries.~~

~~*Add a method to the domain to provide the list of available spaces.~~

