import .aff_coord_space

universes u v w

variables (X : Type u) (K : Type v) (V : Type w) (n : ℕ) (id : ℕ) (k : K)
[inhabited K] [field K] [add_comm_group V] [vector_space K V] [affine_space X K V]

#check linear_map

structure aff_auto :=
(f_v : V → V) 
(f_p : X → X)
(linear : ∃ g : linear_map K V V, ∃ x : V, ∀ v : V, f_v v = g v + x)

structure aff_coord_map :=
(f_v : aff_vec_coord_tuple K n → aff_vec_coord_tuple K n)
(f_p : aff_pt_coord_tuple K n → aff_pt_coord_tuple K n)
(linear_part : ∃ g : linear_map K (aff_vec_coord_tuple K n) (aff_vec_coord_tuple K n), ∀ v : aff_vec_coord_tuple K n, ∃ x, f_v v = g v + x)

structure aff_coord_map' :=
(to_fun : affine_space X K V → affine_space X K V) -- doesn't work. maps one prop to another.

/-
want to say f_v = f_p

want to say f_v is linear up to some translation

v = x - 0

f_v v = f_p x - 0
-/