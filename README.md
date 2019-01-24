# PeirceProject
This repository supports the collaborative development of Pierce, a system for implementing real-world semantics for code. The project name recalls the great American logician, Charles Saunders Peirce, who carried out seminal work on both logic and semiotics: the study of the meanings of symbols.  See https://plato.stanford.edu/entries/peirce-semiotics/. 

## Overview
The aim of the project is to establish formalized *interpretations* of symbolic expressions in code to underpin a theory of the *real-world* as opposed to *programming language* semantics of code. To start, we are focusing on the physical semantics of code for cyber-physicals systems, and for robotics systems, in particular. We hypothesize, and have already produced some substantial evidence for the proposition that, such code is prone to contain many *abstract type errors*. These are errors that arise when the type system of the programming language allows operations to occur that are inconsistent with the *intended* but not formalized or enforced, *real-world interpretations* of such symbolic expressions. 

## Abstract Type Errors
As an example, it is an abstract type error to add two *vector* objects, even if the programming language's type system allows it, if it is intended that those vectors actually belong to different vector spaces. The problem is that it is very common for code to be overly abstracted from the actual mathematics and physics of the domain, and thus underconstrained with respect to what actually makes sense in its domain. 

## Interpretations and Semantics
The concept of an interpretation is taken from work on the semantics of logics, particularly the semantics of predicate and higher order constructive logics, in which the truth of a purely symbolc proposition can only be evaluated with respect to a given *interpretation* that connects symbolic expressions in the logics to objects in some *real-world* domain of discourse. Intepretations are essential for giving expressions in predicate logic a *real-world* semantics. What has long been missing from software is a corresponding notion. We view the code as fundamentally symbolic stuff with some internal type-checking, but that checking in general is entirely insufficient to enforce the constraints incurred when the intended intepretations of symbolic expressions in the code are made clear.

## Automated Construction of Interpretations
This project aims to substantially automate the process of building such interpretations of code. By definition, the code does not contain enough computable information to fully determine an interpretation. For example, a robotics software system might never make explicit and computable the assumptions that are made about what vector spaces certain vectors inhabit. Information of this kind has to be provided by other means. Our interpretation builder uses formal domain models, e.g., of vector spaces, along with an *oracle* to obtain the additional information necessary to construct a proper interpretation of given elements of a code base. One implementation of our oracle asks the programmer for certain relevant additional bits of information such as the space that a given vector object in the code is assumed to inhabit.

## System Architecture

### Code analyzer
### Domain model
### Interpretation
### Semantic oracle

To do: Add diagram here.

## Use Cases
There are many uses cases for such formalized and computable interpretations of symbolic code. One is to check code for the presence of likely abstract type errors. Another is to improve the generation of test cases, to target only those states that a system might encounter in the real world. A third is to improve program understandability by helping to explain the intended real-world meanings of symbolic expressions in code. There are more.

## Who's Involved
The project is run by Kevin Sullivan and Sebastian Elbaum. Our graduate student, Hannah Leung, is carrying out our initial prototyping work as part of her MS Thesis project. Stay tuned for great things.

## Development Infrastructure and Processes
To work on this project requires some set-up, but it's not bad. First, clone the project or fork it depending on your and our workflows. Second, visit the dockerSetup directory and follow the directions there to create a docker image that contains our LLVM-based development environment. Third, from the top-level project directory, launch a corresponding docker container and obtain a bash terminal. In the docker containder, cd into /pierce. This links to the project directory on your host machine from which you launched the docker image. Now cd into the src directory, type "make clean" just to be sure, then "make". The code should build. To run the code, run "../build/ASTMatcher ../inputs/temp.cpp". Now you can make changes to the code on your host machine, then you back into the container and type "make" again. You can use ordinary git workflows, issuing commands on your host machine, to push your changes to github or to post pull request, depending on how we are working together.

## Obsolete 

The rest of these instructions are obsolete and will be updated or deleted soon.

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




