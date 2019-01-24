# PeirceProject
This repository holds artifacts for a UVa Research Project on Real-World Semantics of Code run by Kevin Sullivan and 
Sebastian Elbaum. The aim of the project is to establish formal interpretations to underpin a theory of the real-world semantics of code. As a starting point, we are focusing on the physical semantics of code for cyber-physicals systems, and for robotics systems, in particular. Our graduate student, Hannah Leung, is carry out initial prototyping work as part of her MS Thesis project. The project name recalls the great American logician, Charles Saunders Peirce, who carried out seminal work on semiotics: the study of the meanings of symbols.  See https://plato.stanford.edu/entries/peirce-semiotics/. Stay tuned for great things.

### ASTParser
Here is a description of the ASTParser folder.
```path/to/ASTParser
		|-./src_clang
		|     |-ASTMatcher.cpp
		|-./build
		|       |binary
		|-./inputs
		|	|-vec.h
		|	|-main.cpp
		|-Makefile
```
FindNamedClass.cpp is the file that contains the source code for the Clang standalone tool that can find the class with a specific class name in the AST tree. It is stored in the ./src directory, assuming the current directory is `PierceProject/ASTParser` You can run the following commands to test things out.
```
make
./build/ASTMatcher ./inputs/temp.cpp --

```
This is an example on the `./inputs/temp.cpp` file and the `--` at the end of the command is to tell information about the compilation database. 




