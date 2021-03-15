-- DATA TYPE

/-
A version of the unit type that can
live in any type universe. Adds type
universe parameter to usual unit type.
-/

universe u
inductive uunit : Type u
| star


