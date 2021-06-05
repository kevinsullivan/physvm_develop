import linear_algebra.affine_space.basic
import linear_algebra.basis


namespace aff_fr

universes u v w

variables 
    -- (id : ℕ)
    (X : Type u) 
    (K : Type v) 
    (V : Type w) 
    (n : ℕ) 
    (k : K)
    (ι : Type*)
    (v : ι → V) 
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    [is_basis K v] 
    [affine_space V X]

/-
We define an affine coordinate frame as containing 
an affine 
-/
open list

@[ext]
structure aff_vec_coord_tuple :=
(l : list K)
(len_fixed : l.length = n + 1)
(fst_zero : head l = 0)

/-- type of affine points represented by coordinate tuples -/
@[ext]
structure aff_pt_coord_tuple :=
(l : list K)
(len_fixed : l.length = n + 1)
(fst_one : head l = 1)

mutual inductive affine_coordinate_frame, aff_coord_pt, aff_coord_vec
with affine_coordinate_frame  : Type
| std_frame 
| gen_frame 
    (origin : aff_coord_pt) 
    (basis : ι → aff_coord_vec) 
    (proof_is_basis : is_basis K basis)
with aff_coord_pt : Type
| mk (fr : affine_coordinate_frame) (tuple : aff_pt_coord_tuple K n) : aff_coord_pt
with aff_coord_vec : Type
| mk (fr : affine_coordinate_frame) (tuple : aff_vec_coord_tuple K n)

end aff_fr