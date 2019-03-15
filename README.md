This project is archived. The repo became corrupted and the merge-hannah branch was somehow lost. Please refer to the new Peirce repository for current project status.

# PeirceProject
This repository supports the collaborative development of Pierce, a system for implementing real-world semantics for code. The project name recalls the great American logician, Charles Saunders Peirce, who carried out seminal work on both logic and semiotics: the study of the meanings of symbols.  See https://plato.stanford.edu/entries/peirce-semiotics/. 

## Overview
The aim of the project is to establish formalized *interpretations* of symbolic expressions in code to underpin a theory of the *real-world*, or *physical*, as opposed to *programming language* semantics of code. To start, we are focusing on the physical semantics of code for cyber-physicals systems, and for robotics systems, in particular. We hypothesize, and have already produced some substantial evidence for the proposition that, such code is prone to contain many *physical type errors*. These are errors that arise when the type system of the programming language allows operations to occur that are inconsistent with the *intended* but not formalized or enforced, *physical interpretations* of such symbolic expressions. 

## Abstract Type Errors
As an example, it is a a physical type error to add two concrete instances of some vector class, even if the programming language's type system and the programmer-defined types in the code allow it, if it is intended that those vectors objects in code are intended to represent vectors in different physical spaces, e.g., representing a geometric displacement and a time interval. The problem is that it is very common for code to be overly abstracted from the mathematical physics of the real world, and thus to be underconstrained with respect to computational behaviors that are consistent with the intended physical interpretation of the software. 

## Interpretations and Semantics
The central idea in our work is that to give code a physical semantics, to link it to the level of the physical system that it monitors and controls, requires the notion of an *interpretation*, analogous to that which is used to define the semantics of a logic, such as first-order predicate logic. In such a logic, the truth of a logical proposition is evaluated with respect to a given *interpretation* that connects symbolic terms in the logic to objects in a separate *domain of discourse*. 

Intepretations are essential for giving expressions in predicate logic a semantics. What has long been missing from software is a corresponding notion. We view the code as fundamentally symbolic stuff with internal type-checking and inference rules that define how computations unfold; but such checking and evaluation rules are insufficient to enforce the constraints inherited from the world that the terms in the software are intended to represent. 

## Automated Construction of Interpretations
This project aims to substantially automate the process of building formal, computable interpretations of code to enable new forms of software consistency checking and other capabilities. Code does not contain enough computable information to fully determine an interpretation. For example, a robotics software system might never make explicit and computable the assumptions that are made about what vector spaces certain vectors inhabit. Information of this kind has to be provided by other means. Our interpretation builder uses interchangeable *oracle* objects to obtain additional information necessary to construct formalized interpretations of selected elements in code. One implementation of our oracle just asks the programmer for relevant additional bits of information such as the space that a given vector object in the code is assumed to inhabit.

## Overall Function of Demonstration Prototype
What we have demonstrated is the ability to select C++ code elements that implement certain physically relevant comptuations, particularly ones involving vector spaces and vector operations. Code elements representing vectors and operations on them are mapped to corresponding elements in the language of a constructive logic proof assistant, a kind of software systems that is now being used not only for formal specification and verification of software, but also to formalize abtract mathematics, including the kinds of mathematics central to mathematical physics. Our near- to mid-term aim is to show the feasibility of constructing, largely automatically, interpretations of code that carry out computations important in classical dynamics. Beyond mere checking of *code* for consistency with the constraints of mathematical physics, we anticipate that this work will enable reasoning *in physical domain terms* about system behaviors driven by underlying software. 

Making formal, computable connections between code and physics is essential to effective development and validation of future cyberphysical, especially robotic, systems. This project aims to link code to various mathematical formalisms critical for any effective reasoning about system properties. Such formalisms include vector, affine, and, in particular, Euclidean spaces, and, for systems that experience relativistic effects, Minkoski spaces. This work is expected to lead to a significant and extensive generalization of previous work on adding single-dimensional physical units to code, and to make explcit deep connections to the mathematical physics underlying such metrological efforts.

## System Architecture

### Code analyzer

Based on LLVM and on the Clang Tooling framework, in particular.

### Domain model

Currently a mutable store of Euclidean space types (e.g., Vector, Point), and of instances that correspong to code expressions that are intended to represent abstract objects of these types.

### Interpretation

An associative store that links code elements, identified by what we think of as *code coordinates*, to objects in the domain.

### Semantic oracle

Currently queries user interactively to provide additional information needed, which can be though of as code annotations, to fully construct a desired interpretation.

### Clients and Use Cases

By *clients* we meantools that use interpretations to provide fundamental new software engineering capabilities. Chief among these are checking of code for abstract type errors. Another is to improve the generation of test cases to target only those states that a system might encounter in the real world. A third is to improve program understandability by helping to explain the intended real-world meanings of symbolic expressions in code. A fourth is to optimize physical simulations given the added constraints that the real-world imposes on the permissible behaviors of a software system. There are more.


### Architecture diagram
![ArchitectureDiagram](https://github.com/kevinsullivan/Pierce/doc/images/architecture.png)

## Who's Involved
The project is run by Kevin Sullivan and Sebastian Elbaum. Our graduate student, Hannah Leung, is carrying out our initial prototyping work as part of her MS Thesis project. John Knight and Jian Xiang along with Kevin Sullivan were responsible for early development of many of the ideas that are still central to this work.

## Development Infrastructure and Processes
To work on this project requires some set-up, but it's not bad. First, clone the project or fork it depending on your and our workflows. Second, visit the dockerSetup directory and follow the directions there to create a docker image that contains our LLVM-based development environment. Third, from the top-level project directory, launch a corresponding docker container and obtain a bash terminal. In the docker containder, cd into /pierce. This links to the project directory on your host machine from which you launched the docker image. Now cd into the src directory, type "make clean" just to be sure, then "make". The code should build. To run the code, run "../build/ASTMatcher ../inputs/temp.cpp". Now you can make changes to the code on your host machine, then you back into the container and type "make" again. You can use ordinary git workflows, issuing commands on your host machine, to push your changes to github or to post pull request, depending on how we are working together.

## Organization of the project.

Here is a description of the hierarchy of the files.
```
pwd = path/to/Pierce

    ./|--/src(contains the source files of the clang tool)
      |
      |--/inputs(contains code we experiment on)
      |
      |--/dockerSetup(contians instructions for setting up the docker container)
      |
      |--/build(contians the binary format of the bool)
      |
      |--README(Introduction for the project)
      |
      |--TODO.txt(maintains the todos along the development)
```
## Run the program

First, make sure you followed the instructions in the `./dockerSetup` to setup the docker container properly. Then go to the top level directory of this repo.
Simply run the following command to how the tool works.
```
cd ./src
make
../build/ASTMatcher ../inputs/temp.cpp --
```
This is an example on the `./inputs/temp.cpp` file and the `--` at the end of the command is to tell information about the compilation database. 





