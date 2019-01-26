TODO:


Hannah's Todo

* get the name, file, line no. of each vector instance
* bind the parameters of vec_add expression
* add interpretation for expression
* generate lean file for analysis
* make oracle ask about declarations by name, file, line number
* fix dockerfile to install Lean and its math libraries, e.g., using elan
* fix oracle so that it does what it says it's doing: return selected space
* fix makefile: use cmake and ninja

DONE:

~~*Do the same stuff for expressions that we just did for vector instances.~~

~~*Implement domain.isConsistent. This means iterating over the domain objects and writing out a corresponding Lean file and sending it off to the type checker.~~

~~*Connect "ASTNode" object to the Clang AST node objects that you're
finding in the code.~~

~~*Update the oracle so that it asks you about which spaces vectors belong to.~~

~~*Update readme file.~~

~~*Update .gitignore so that we don't push binaries.~~

~~*Add a method to the domain to provide the list of available spaces.~~

