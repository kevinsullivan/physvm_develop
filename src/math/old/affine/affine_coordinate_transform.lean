import .affine_coordinate_framed_space_lib --linear_algebra.affine_space.basic
import 
    linear_algebra.affine_space.basic
    linear_algebra.affine_space.affine_equiv 
    linear_algebra.nonsingular_inverse
    linear_algebra.matrix
--    linear_algebra.


open_locale affine

namespace aff_trans

open aff_fr
open aff_lib
universes u 
variables 
    (K : Type u)
    (n : ℕ )
    [inhabited K]
    [field K]
    (fr1 : affine_coord_frame K n) 
    (fr2 : affine_coord_frame K n) 
    (cv1 cv2 : aff_coord_vec K n fr1) 
    (cp1 cp2 : aff_coord_pt  K n fr2)

abbreviation 
    affine_coord_frame_transform 
    := 
    (aff_coord_pt K n fr1) 
    ≃ᵃ[K] 
    (aff_coord_pt K n fr2)
    
abbreviation
    affine_coord_space_transform
    (sp1 : affine_coord_space K n fr1)
    (sp2 : affine_coord_space K n fr2)
    := 
    affine_coord_frame_transform K n fr1 fr2

variables 
    (sp1 : affine_coord_space K n fr1)
    (sp2 : affine_coord_space K n fr2)
  (a1 : affine_coord_frame_transform K n fr1 fr2)
  (a2 : affine_coord_space_transform K n fr1 fr2 sp1 sp2)


abbreviation
    affine_tuple_space_transform
    := 
    (aff_pt_coord_tuple K n)
    ≃ᵃ[K] 
    (aff_pt_coord_tuple K n)


def affine_coord_space_transform.domain_frame
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
    {from_sp : affine_coord_space K n fr1}
    {fr2 : affine_coord_frame K n}
    {to_sp : affine_coord_space K n fr2}
    (tr : affine_coord_space_transform K n fr1 fr2 from_sp to_sp)
    := fr1

def affine_coord_space_transform.codomain_frame
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
    {from_sp : affine_coord_space K n fr1}
    {fr2 : affine_coord_frame K n}
    {to_sp : affine_coord_space K n fr2}
    (tr : affine_coord_space_transform K n fr1 fr2 from_sp to_sp)
    := fr2

def affine_coord_space_transform.domain_space
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
    {from_sp : affine_coord_space K n fr1}
    {fr2 : affine_coord_frame K n}
    {to_sp : affine_coord_space K n fr2}
    (tr : affine_coord_space_transform K n fr1 fr2 from_sp to_sp)
    := from_sp

def affine_coord_space_transform.codomain_space
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
    {from_sp : affine_coord_space K n fr1}
    {fr2 : affine_coord_frame K n}
    {to_sp : affine_coord_space K n fr2}
    (tr : affine_coord_space_transform K n fr1 fr2 from_sp to_sp)
    := to_sp


/-
(
                matrix.mul_vec 
                (affine_tuple_coord_frame.get_basis_matrix fr)
                (affine_vec_coord_tuple.to_indexed 
                  ((fr.origin -ᵥ pt_zero K n) : aff_vec_coord_tuple K n))
              ) --: 
-/

variables 
  (a : square_matrix K n) 
  (a_i : matrix (fin n) (fin n) K) 
  (i : col_matrix K n) 
  (i_i : fin n → K)


#check matrix.mul_vec a_i i_i

#check a_i

#check  (matrix.mul_vec_lin a_i : _)
#check  (matrix.mul_vec_lin a_i : _).map_add


    
/-
IS THIS IN MATHLIB ALREADY?
NOT matrix.diag_one??
-/
attribute [reducible]
def square_matrix.eye
    (K : Type u)
    (n : ℕ)
    [inhabited K] 
    [field K] 
    : square_matrix K n
    := 
    λ i j,
    if i = j then 1 else 0

attribute [reducible]
noncomputable def affine_tuple_space.to_base_space
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
   -- [affine_space (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n)]
    (fr : affine_tuple_coord_frame K n)
    : affine_tuple_space_transform K n
    :=
    ⟨
      ⟨
        λ p ,
          (matrix.mul_vec 
                (affine_tuple_coord_frame.get_basis_matrix fr)
                ↑((fr.origin -ᵥ pt_zero K n) : aff_vec_coord_tuple K n)
           : aff_vec_coord_tuple K n) 
          +ᵥ
          (⟨matrix.mul_vec 
            (affine_tuple_coord_frame.get_basis_matrix fr)
            ↑p⟩ : aff_pt_coord_tuple K n),
        λ p,
          (vec_neg K n (
            matrix.mul_vec 
            (affine_tuple_coord_frame.get_basis_matrix fr)⁻¹
            ↑((fr.origin -ᵥ pt_zero K n) : aff_vec_coord_tuple K n)
            : aff_vec_coord_tuple K n)) +ᵥ
          ( (⟨matrix.mul_vec 
            (affine_tuple_coord_frame.get_basis_matrix fr)⁻¹
            ↑p⟩) : aff_pt_coord_tuple K n
          ),
          sorry,
          sorry
      ⟩,
      ⟨
        λ v,
          (matrix.mul_vec 
          (affine_tuple_coord_frame.get_basis_matrix fr)
          (↑v) : aff_vec_coord_tuple K n),
        sorry,
        sorry,
        λ v,
          (matrix.mul_vec 
          (affine_tuple_coord_frame.get_basis_matrix fr)⁻¹
          (↑v) : aff_vec_coord_tuple K n),
        sorry,
        sorry⟩ ,
      sorry
    ⟩




attribute [reducible]
noncomputable def affine_tuple_space.to_derived_space
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
   -- [affine_space (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n)]
    (fr : affine_tuple_coord_frame K n)
    : affine_tuple_space_transform K n
    := 
    (affine_tuple_space.to_base_space fr)⁻¹ 

attribute [reducible]
noncomputable def affine_tuple_space.standard_transform
  := 
  affine_tuple_space.to_derived_space (affine_tuple_coord_frame.standard K n)

attribute [reducible]
def affine_tuple_space_transform.to_coord_transform
    {fr1 : affine_coord_frame K n}
    (from_sp : affine_coord_space K n fr1)
    {fr2 : affine_coord_frame K n}
    (to_sp : affine_coord_space K n fr2)
    (tr : affine_tuple_space_transform K n)
    :
    affine_coord_space_transform K n fr1 fr2 from_sp to_sp
    := 
    ⟨
      ⟨
        λ p,⟨tr p.1⟩ ,
        λ p,⟨tr⁻¹ p.1⟩,
        sorry,
        sorry 
      ⟩ ,
      ⟨
        λ v,⟨tr.linear v.1⟩,
        sorry,
        sorry,
        λ v,⟨tr.linear⁻¹ v.1⟩,
        sorry,
        sorry
      ⟩,
      sorry
    ⟩

attribute [reducible]
noncomputable mutual def 
  affine_coord_space.build_from_to_standard_transform,
  affine_coord_space.fold_tuple_from_to_standard_transforms
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {initial_fr : affine_coord_frame K n}
    (initial_sp : affine_coord_space K n initial_fr)
with affine_coord_space.build_from_to_standard_transform : 
  list (aff_fr.affine_coord_frame K n) → 
                                  (affine_coord_space_transform K n
                                      initial_fr
                                      (affine_coord_frame.standard K n)
                                      initial_sp
                                      (affine_coord_space.mk_with_standard K n))
| [] := 
  let tr := (affine_tuple_space.to_base_space (affine_coord_frame.get_coords initial_fr)) in
    affine_tuple_space_transform.to_coord_transform K n _ _ tr
| (h::t) := 
  let tr := (affine_tuple_space.to_base_space (affine_coord_frame.get_coords initial_fr)) in 
  let trf := tr.trans (affine_coord_space.fold_tuple_from_to_standard_transforms t) in
    affine_tuple_space_transform.to_coord_transform K n _ _ tr
with affine_coord_space.fold_tuple_from_to_standard_transforms :
  list (aff_fr.affine_coord_frame K n) → 
                                  (affine_tuple_space_transform K n)
| [] := (affine_tuple_space.standard_transform K n )
| (h::t) := let tr := (affine_tuple_space.to_base_space (affine_coord_frame.get_coords initial_fr)) in 
      tr.trans 
          (affine_coord_space.fold_tuple_from_to_standard_transforms t)

attribute [reducible]
noncomputable mutual def 
  affine_coord_space.build_standard_to_to_transform,
  affine_coord_space.fold_tuple_to_to_standard_transforms
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {to_fr : affine_coord_frame K n}
    (to_sp : affine_coord_space K n to_fr)
with affine_coord_space.build_standard_to_to_transform : 
  list (aff_fr.affine_coord_frame K n) → 
                                  (affine_coord_space_transform K n
                                      (affine_coord_frame.standard K n)
                                      to_fr
                                      (affine_coord_space.mk_with_standard K n))
                                      to_sp
| [] := 
  let tr := (affine_tuple_space.to_base_space (affine_coord_frame.get_coords to_fr)) in
    ((affine_tuple_space_transform.to_coord_transform K n to_sp (affine_coord_space.mk_with_standard K n) tr).symm)
| (h::t) := 
  let tr := (affine_tuple_space.to_derived_space (affine_coord_frame.get_coords to_fr)) in 
  let trf := tr.trans (affine_coord_space.fold_tuple_to_to_standard_transforms t) in
    (affine_tuple_space_transform.to_coord_transform K n to_sp (affine_coord_space.mk_with_standard K n) tr).symm
with affine_coord_space.fold_tuple_to_to_standard_transforms :
  list (aff_fr.affine_coord_frame K n) → 
                                  (affine_tuple_space_transform K n)
| [] := (affine_tuple_space.standard_transform K n )
| (h::t) := 
  let tr := (affine_tuple_space.to_derived_space (affine_coord_frame.get_coords to_fr)) in 
      tr.trans 
          (affine_coord_space.fold_tuple_to_to_standard_transforms t)

attribute [reducible]
noncomputable def affine_coord_space.build_transform
    (sp1 : affine_coord_space K n fr1)
    (sp2 : affine_coord_space K n fr2)
    : affine_coord_space_transform K n fr1 fr2 sp1 sp2
    := 
    let path := affine_coord_space.find_transform_path' sp1 sp2 in
    --let from_head_eq_fr1 : fr1 = path.from_.head := sorry in
    --let to_head_eq_fr2 : fr2 = path.to_.head := sorry in
    let from_ := (affine_coord_space.build_from_to_standard_transform sp1 path.to_.tail) in
    let to_ := (affine_coord_space.build_standard_to_to_transform sp2 path.to_.tail) in
      from_.trans to_

    --([] : list (square_matrix K (n+1)))

notation t1⬝t2 := t1.trans t2
--notation t1•t2 := t1.trans t2

def tran_times_vec 
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
   -- (from_sp : affine_coord_space K n fr1)
    {fr2 : affine_coord_frame K n}
   -- (to_sp : affine_coord_space K n fr2)
   (tr : affine_coord_frame_transform K n fr1 fr2)
   (p : aff_coord_vec K n fr1)
   : aff_coord_vec K n fr2
   := tr (p +ᵥ (⟨pt_zero K n⟩ : aff_coord_pt K n fr1))
        -ᵥ (⟨pt_zero K n⟩ : aff_coord_pt K n fr2)

--notation t1⬝t2 := tran_times_vec t1 t2
--notation t1⬝t2 := t1.to_equiv t2

end aff_trans