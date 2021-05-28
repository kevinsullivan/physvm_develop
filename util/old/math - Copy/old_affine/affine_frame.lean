import tactic.ext linear_algebra.affine_space.basic
import algebra.module linear_algebra.basis
import .affine_coordinate_space 


/-
This file defines:

(1) a generic affine frame: an origin in X and a basis for V.
(2) new types that wrap values in X and V with a polymorphic frame argument 
(3) lifting of operations on points and vectors to this derived type
(4) a proof that the lifted point and vector objects for an affine space
-/

namespace affine_frame

universes u v w x

variables 
    (X : Type u) 
    (K : Type v) 
    (V : Type w) 
    (n : ℕ) 
    (k : K)
    (ι : Type*)
    (s : finset ι) 
    (g : ι → K) 
    (v : ι → V) 
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    [is_basis K v] 
    [affine_space V X]

open vecl

/-
An affine frame comprises an origin point
and a basis for the vector space.
-/
structure affine_frame :=
(origin : X)
(basis : ι → V)
(proof_is_basis : is_basis K basis)

/-
Code to manufacture a standard basis for a given affine space.
-/
abbreviation zero := zero_vector K n

def list.to_basis_vec : fin n → list K := λ x, (zero K n).update_nth (x.1 + 1) 1

lemma len_basis_vec_fixed (x : fin n) : (list.to_basis_vec K n x).length = n + 1 := sorry

lemma head_basis_vec_fixed (x : fin n) : (list.to_basis_vec K n x).head = 0 := sorry

def std_basis : fin n → aff_vec_coord_tuple K n :=
λ x, ⟨list.to_basis_vec K n x, len_basis_vec_fixed K n x, head_basis_vec_fixed K n x⟩

lemma std_is_basis : is_basis K (std_basis K n) := sorry

/-
Here we equip any generic affine coordinate space with a standard frame
-/
def aff_coord_space_std_frame : 
    affine_frame (aff_pt_coord_tuple K n) K (aff_vec_coord_tuple K n) (fin n) := 
        ⟨pt_zero K n, std_basis K n, std_is_basis K n⟩

end affine_frame





