# PeirceProject
This repository supports the collaborative development of Pierce, a system for implementing a physical or other exterior semantics for code. The project name recalls the great American logician, Charles Saunders Peirce, who carried out seminal work on logic and semiotics: the study of the meanings of symbols.  See https://plato.stanford.edu/entries/peirce-semiotics/. 

## Overview
The semantics of propositional, predicate, and constructive logic are defined in terms of
*interpretations*. An interpretation is a function from symbols *within* a logical expression to meanings in some exterior *domain of discourse*. Such a domain of discourse constitutes a realm that lies beyond the symbols and the rules of deduction internal to the logic itself.

A programming language is of course just a logic, and a program is an expression in such a logic. And yet, for decades, the concept of the semantics of a programming language, and of an expression in such a logic, has been defined in terms of the rules of deduction (and in paritcular the rules of computation) *internal* to the logic. What is fundamentally missing from this account of the semantics of software is any notion of a formal *interpretation* of a given program, in the sense of an explication of the intended meanings, in some domain of discourse *exterior to the code*, of the logical symbols within the code.

This project aims to establish a new formal semantics of code rooted in the definition of *interpretations,* mapping symbolic expressions in code to objects in domains of discourse *exterior to the code and the underlying programming language and system*. 

To start, we are focusing on the physical semantics of code for cyber-physicals systems, and for robotics systems, in particular. We hypothesize, and have already produced some substantial evidence for the proposition that, such code is prone to contain many *abstract type errors*. These are errors that arise when the type system of the programming language allows operations to occur that are inconsistent with the *intended* but not formalized or enforced, *real-world interpretations* of such symbolic expressions. 

## Abstract Type Errors
Software is typically over-abstracted from its intended domain of discourse. A significant body of work has focused on the problem that when physical quantities are represented by numberical symbolic expressions in code, corresponding physical units are often abstracted away. As a result, *internally* well typed code can perform operations that have no meanings in corresponding *external* domain. The Mars Polar Orbiter mission was famously lost due to the execution of an internally well typed computation that had no physical meaning due to mismatched assumptions about the units in which quanitities were expressed.

We refer to such errors as *abstract type errors*. These are type errors *in the domain of discourse* as represented by symbols in the code. Such errors cannot be detected by programming language type systems because, by our definition, they involve information that has been abstracted away in the mapping of the domain of discourse to its symbolic representation in the logic of a programming language.  

## Automated Construction of Interpretations
This project aims to substantially automate the process of constructing formal interpretations of code. By definition, the code does not contain enough computable information to fully determine an interpretation. On the other hand, because an interpretation is a mapping from expressions in the code to meanings in another domain, the code provides a precise map of where additional information needs to be provided to fully specify the intended interpretation of the code. Our approach thus involves analysis of the code and appeal to an external *oracle*, which can take different forms for different applications, that serves to provide the additional information needed to establish a complete, formal interpretation of of given system. 

## A New Approach to Reasoning About Software and the Systems it Runs

It is impossibly to reason adequately from software that is stripped of essential information from its corresponding domain of discourse. Are there abstract type errors in a given system? No amount of ordinary code analysis can say, because the information necessary to make such a decision is either missing from the code entirely, or it is in a form (e.g., comments or variable identifiers) that is generally not carefully engineered to support rigorous analysis. 

For example, a robotics software system might never make critical assumptions explicit about what vector spaces certain vectors belong to that are represented in the code. Does this scalar represent a temporal duration or a distance in a geometric space? Information of this kind, that has been stripped from the code, has to be provided by other means. Our interpretation builder uses formal domain models, e.g., of vector spaces, along with an *oracle* to obtain the additional information necessary to construct a proper interpretation of given elements of a code base. What our system builds, then, are fully formal, complete interpretations of selected *aspects* of code, such as its representation of physical quantities. 

With such an interpretation in hand for a given piece of software, new kinds of reasoning, and new software and systems engineering capabilities, become possible. Our first application is abstract type-checking. We achieve this capability by mapping selected, physically relevant aspects of source code (currently for C++ robotics code) to corresponding expressions in an abstract mathematical language, currently of affine and Euclidean space expressions formalized in the expressive logic of a constructive logic proof assistant. We then rely on the foundational type checking capabilities of these tools to type check expressions *lifted from the code to interpretations in the domain* for abstract type errors.

Prior work has confirmed the difficulty of manually annotating large bodies of code with meta-data for physical units. Our work shows that it is at least possible to take advantage of the sophsticated *type inference* capabilites of such checkers to dramatically reduce the burden of annotating code without writing a single line of additional inferencing software.

There are many directions for future work, building on our concept of software interpretations and on our demonstration prototype system.

## System Architecture

### Parser

We craft code-specific pattern matchers using Clang tooling to project domain-relevant abstract syntax tree elements from code.

### Interpretation builder

We establish interpretations for each such AST element. An interpretation comprises, for each AST element (generally a subtree of the overall AST), an isomorphic tree of *code coordinates*, an isomorphic tree of *domain expressions*, and an isomorphic tree of *interpretation objects*, with relational mappings connecting all of these objects in forwards and backwards directions. An oracle is invoked to create domain objects for each selected code object. Oracles implement a simple oracle interface. We currently have oracles that query a human analyst for the required additional information. 

### Clients and Use Cases

By *clients* we meantools that use interpretations to provide fundamental new software engineering capabilities. Chief among these are checking of code for abstract type errors. Another is to improve the generation of test cases to target only those states that a system might encounter in the real world. A third is to improve program understandability by helping to explain the intended real-world meanings of symbolic expressions in code. A fourth is to optimize physical simulations given the added constraints that the real-world imposes on the permissible behaviors of a software system. There are more.


### Development Infrastructure and Processes
The best way to work on this project is to download our PeirceVM: an Ubuntu VM completely set up for development and testing of this project. It includes Clang, Lean, required libraries, VSCode configured for C++ development, and so on. It's about a 30GB VM. Kevin Sullivan routinely works on this project on a MacBook Pro laptop. Once you download the VM, you launch it, log into to a pre-established account, cd into the project directory, do *git pull* with your own GitHub credentials, launch VS Code from the project directory, do a CTRL-SHIFT-b to compile the code, and you are then up and running. 

### Run the program

Go to the top level directory of this repo. You can then run the command, *build/ASTMatcher inputs/temp.4.cpp --*, to run the interpretation builder on a simple C++ program implementing a few basic vector space operations. 


## Significance to Systems Engineering

Our first use cases for this work will focus on robotics code, e.g., for UAV drones, programmed in C++ using ROS. The expected significance of this work for the systems engineering community is that it finally gives us a way to lift knowledge from code to knowledge expressed in *physical* terms. By lifting code abstractions to Euclidean space abstractions, for example, we represent critical what the code is doing in the language of mathematical physics rather than in the logic of some arcane programming language. We think that this work has the potential to provide systemms engineers with significant insights into what the software in their systems is doing by explaining what it means not in the language of code but in the language of the phsysical domain of discourse. 

## Who's Involved
The project is run by Kevin Sullivan and Sebastian Elbaum. Our graduate student, Hannah Leung, is carrying out our initial prototyping work as part of her MS Thesis project. Stay tuned.

## Acknowledgements

Kevin Sullivan's work on this project has been supported by the Systems Engineering Research Center. (A proper, approved acknowledgement wil be provided here.) This work draws heavily on prior work by both PIs, including Sullivan's work with Jian Xiang (now a postdoc at Harvard) and John Knight, and Elbaum's work on efficient units checking. We acknolwege our collaborators' essential prior contributions to this line of work.
