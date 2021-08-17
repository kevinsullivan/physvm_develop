import linear_algebra.affine_space.basic

universes u v w

open_locale affine
/-
A polymorphic affine space type with
explicit type parameters
- dimension, dim; 
- "point" set, X;
- scalar set, K; 
- module (e.g., "vector" set), V

The typeclass mechanism is used to find
proofs that confirm that the specified 
type does actually constitute an affine
space type.
-/

--open_locale affine

structure affine_space_type
    --(id : ℕ)
    (X : Type u)
    (K : Type v)
    (V : Type w)
    [ring K] 
    [add_comm_group V] 
    [module K V]  
    [affine_space V X]
