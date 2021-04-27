# Knowledge and Skills for Exam 1

NB: Until Prof. Sullivan announces on Collab that this document is ready for your review, you should not rely on it as a complete or as an accurate description of topics that might be covered on exam1.

# Boolean algebra

Know solidly the truth tables for the following Boolean operations and how to specify them in Lean. The operators with a * next to their Lean names are not provided by the Lean library; rather, you'd have to implement them (and their notations) yourself to use them.

Name    | Symbol    | Lean name | Description
--------|-----------|---------- |------------------------------
or      |   ∨       | bor       | disjunction 
and     |   ∧       | band      | conjunction
not     |   ¬       | bnot      | negation 
implies |   →       | bimp*     | implies, conditional, if/then  
equiv   |   ↔       | iff       | if and only if, equivalent to
xor     |   ⊕      | bxor*     | exclusive or
nand    |   ↑, ⊼    | bnand*    | not and, negation of conjunction
nor     |   ↓, ⊽    | bnor*     | not or, negation of disjunction
xnor    |   ⊙      | bxnor*    | not xor, negation of xor

## Inductive Data Types

- Sum, product, and sum of product types
- Semantics of inductive data type definitions
   - Disjointness and injectivity of constructors
   - Smallest set closed under finite applications of constructors
- Polymorphic data types
- Type universes
- Recursive data types
- Type-guided top down refinement of terms of given types 
- Type-checked bottom-up composition of terms of given types
- Standard *abstract data types*: type definitions and operations
   - empty
   - unit
   - bool
   - prod
   - option
   - sum
   - nat
   - list
   - tree

## Function Types
- Lambda abstractions as terms that represent functions
- Function application, left associativity thereof
- Various syntactic forms for defining functions
  - lambda abstraction, anonymous function values
  - function definition by cases
  - C-style function definitions
  - How to define recursive functions
  - How to specify higher-order function types and implementations
- Function evaluation, and partial evaluation, in particular
- Polymorphic type definitions and implicit type arguments 
- How to use pattern matching to destructure values of given types
- Totality of functions in constructive logic (including Lean)
- Using option types to specify partial functions as total functions
- Using sum types to specify partial functions with error returns
- 
  