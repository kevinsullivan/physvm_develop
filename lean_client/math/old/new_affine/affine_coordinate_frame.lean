import .affine_coordinate_space 

/-
This file exports 
- std_basis, given finite index set, return standard vector-space basis
- std_frame, return standard frame on d-dimensional affine space
-/

/-
We've shown that <aff_pt_coord_tuple, aff_vec_coord_tuple> 
constitutes an  affine space.There's no notion of a frame at this point. 
However,  we can endow such a space with a standard frame, taking the point,
<1, 0, ..., 0> as the standard origin and the vectors, <0, 1, 0, ...>,
..., <0, 0, ..., 1> as the standard basis for the vector space. To 
this end, we now define what it means to be a frame for an affine space
and we provide a function for obtaining a standard basis for any given
space of this kind.
-/


namespace aff_basis

universes u v w x

variables (X : Type u) (K : Type v) (V : Type w) (n : ℕ) (k : K)
[inhabited K] [field K] [add_comm_group V] [vector_space K V] [affine_space V X]

open vecl

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

end aff_basis

/-
What's funny is that we don't actually have an explicit abstraction of 
affine coordinate space, e.g., as a type.
-/