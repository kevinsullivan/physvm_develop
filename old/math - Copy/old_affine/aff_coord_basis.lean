import .aff_coord_space .affine .list_stuff data.real.basic

namespace aff_basis
universes u v w x

variables (X : Type u) (K : Type v) (V : Type w) (n : ℕ) (k : K)
[inhabited K] [field K] [add_comm_group V] [vector_space K V] [affine_space X K V]

abbreviation zero := list.field_zero K n

def list.to_basis_vec : fin n → list K := λ x, (zero K n).update_nth (x.1 + 1) 1

lemma len_basis_vec_fixed (x : fin n) : (list.to_basis_vec K n x).length = n + 1 := sorry

lemma head_basis_vec_fixed (x : fin n) : (list.to_basis_vec K n x).head = 0 := sorry

def std_basis : fin n → aff_vec_coord_tuple K n :=
λ x, ⟨list.to_basis_vec K n x, len_basis_vec_fixed K n x, head_basis_vec_fixed K n x⟩

lemma std_is_basis : is_basis K (std_basis K n) := sorry

def std_frame : affine_frame (aff_pt_coord_tuple K n) K (aff_vec_coord_tuple K n) (fin n) := ⟨pt_zero K n, std_basis K n, std_is_basis K n⟩

noncomputable def r3_std_frame := std_frame ℝ 3

def std_origin : pt_with_frame (aff_pt_coord_tuple K n) K (aff_vec_coord_tuple K n) (fin n) (std_frame K n) := ⟨pt_zero K n⟩
--TODO: fix this

-- nothing in the phys layer should be called "aff_pt_coord_tuple K n" or "aff_vec_coord_tuple K n"
end aff_basis