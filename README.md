# PeirceProject
This repository supports the collaborative development of Pierce, a system for implementing real-world semantics for code. The project is run by Kevin Sullivan and Sebastian Elbaum. The aim of the project is to establish formalized *interpretations* of symbolic expressions in code to underpin a theory of the real-world semantics of such code. To start, we are focusing on the physical semantics of code for cyber-physicals systems, and for robotics systems, in particular. We hypothesize, and have already shown substantial evidence for the proposition that, such code is prone to contain many *abstract type errors*. These are errors that occur when the type system of the programming system allows operations to occur that are inconsistent with the *intended* but not formalized or enforced, *real-world interpretations* of such symbolic expressions. 

Our graduate student, Hannah Leung, is carry out initial prototyping work as part of her MS Thesis project. The project name recalls the great American logician, Charles Saunders Peirce, who carried out seminal work on both logic and semiotics: the study of the meanings of symbols.  See https://plato.stanford.edu/entries/peirce-semiotics/. Stay tuned for great things.

To work on this project requires some set-up, but it's not bad. First, clone the project or fork it depending on your and our workflows. Second, visit the dockerSetup directory and follow the directions there to create a docker image that contains our LLVM-based development environment. Third, from the top-level project directory, launch a corresponding docker container and obtain a bash terminal. In the docker containder, cd into /pierce. This links to the project directory on your host machine from which you launched the docker image. Now cd into the src directory, type "make clean" just to be sure, then "make". The code should build. To run the code, run "../build/ASTMatcher ../inputs/temp.cpp". Now you can make changes to the code on your host machine, then you back into the container and type "make" again. You can use ordinary git workflows, issuing commands on your host machine, to push your changes to github or to post pull request, depending on how we are working together.

[The rest of these instructions are obsolete and will be updated soon.]

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




