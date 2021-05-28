import tactic.ext linear_algebra.affine_space.basic
import algebra.module linear_algebra.basis


/-
This file defines:

(1) a generic affine frame: an origin in X and a basis for V.
(2) new types that wrap values in X and V with a polymorphic frame argument 
(3) lifting of operations on points and vectors to this derived type
(4) a proof that the lifted point and vector objects for an affine space
-/

universes u v w

variables (X : Type u) (K : Type v) (V : Type w) (ι : Type*)
[ring K] [add_comm_group V] [module K V]

variables (s : finset ι) (g : ι → K) (v : ι → V) [is_basis K v] [affine_space V X]

--open_locale big_operators

structure affine_frame :=
(origin : X)
(vec : ι → V)
(basis : is_basis K vec)



