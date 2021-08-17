import .affine_coordinate_framed_space_lib
import .affine_coordinate_transform
import linear_algebra.affine_space.basic
import topology.metric_space.emetric_space
import analysis.normed_space.inner_product
import data.complex.is_R_or_C
import topology.metric_space.pi_Lp
import analysis.special_functions.trigonometric
import .affine_euclidean_space

universes u v w
open aff_fr aff_lib aff_trans
open_locale big_operators affine
--set_option class.instance_max_depth 100
--
namespace eucl_lib

variables 
  (K : Type u) 
  [inhabited K] 
  [is_R_or_C K]
  [ring K]
  [field K] 
  (n : ℕ) 
  (fr : affine_coord_frame K n)
  [add_comm_group (aff_coord_vec K n fr)] 
  --[module K (aff_coord_vec K n fr)]  
  --[vector_space K (aff_coord_vec K n fr)]
  [affine_space (aff_coord_vec K n fr) (aff_coord_pt K n fr)]
  [emetric_space (aff_coord_pt K n fr)]
  [inner_product_space K (aff_coord_vec K n fr)]
  
  [add_comm_group (aff_vec_coord_tuple K n)] 
  [affine_space (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n)]
  [emetric_space (aff_pt_coord_tuple K n)]
  [inner_product_space K (aff_vec_coord_tuple K n)]
  (rfr : affine_coord_frame ℝ n)


structure affine_euclidean_space 
  extends affine_coord_space K n fr
  := mk ::

instance euclidean_to_affine : has_coe (affine_euclidean_space K n fr) (affine_coord_space K n fr)  :=
⟨λ es : (affine_euclidean_space K n fr), (es.1 : (affine_coord_space K n fr))⟩--⟨λ b, b = tt⟩

noncomputable
def affine_euclidean_space.standard_space
    := affine_euclidean_space K n (affine_coord_frame.standard K n)

attribute [reducible]
noncomputable
def affine_euclidean_space.mk_with_standard
    : affine_euclidean_space.standard_space K n
    := ⟨(aff_lib.affine_coord_space.mk_with_standard K n)⟩

structure affine_euclidean_space.angle 
  :=
  (val : ℝ)--change this to a properly constrained quotient type of ℝ 

noncomputable
def real_affine_coord_vec.compute_angle
    (v1 : aff_coord_vec ℝ n rfr)
    (v2 : aff_coord_vec ℝ n rfr)
    : affine_euclidean_space.angle
    := 
      ⟨real.arccos ⟪v1,v2⟫/∥v1∥*∥v2∥⟩

structure affine_euclidean_rotation
  :=
  (r : affine_tuple_basis ℝ n)
  (normone : ∀ i : fin n, ∥r i∥ = 1)
  (b : ∀ i j : fin n, i≠j → ⟪r i,r j⟫ = 0)

structure affine_euclidean_orientation
  :=
  (r : affine_tuple_basis ℝ n)
  (normone : ∀ i : fin n, ∥r i∥ = 1)
  (b : ∀ i j : fin n, i≠j → ⟪r i,r j⟫ = 0)

variables 
    (fr1 : affine_coord_frame ℝ n) 
    (fr2 : affine_coord_frame ℝ n) 
    (cv1 cv2 : aff_coord_vec ℝ n fr1) 
    (cp1 cp2 : aff_coord_pt  ℝ n fr1)
   -- [add_comm_group (aff_coord_vec ℝ n fr1)] 
   -- [semimodule ℝ  (aff_coord_vec ℝ n fr1)] 
    --[module ℝ  (aff_coord_vec ℝ n fr1)] 
    [vector_space ℝ  (aff_coord_vec ℝ n fr1)] 
    [affine_space (aff_coord_vec ℝ n fr1) (aff_coord_pt ℝ n fr1)]
    [emetric_space (aff_coord_pt ℝ n fr1)]
    [inner_product_space K (aff_coord_vec ℝ n fr1)]
    --[add_comm_group (aff_coord_vec ℝ n fr2)] 
   -- [semimodule ℝ  (aff_coord_vec ℝ n fr2)] 
   -- [module ℝ  (aff_coord_vec ℝ n fr2)] 
    [vector_space ℝ  (aff_coord_vec ℝ n fr2)] 
    [affine_space (aff_coord_vec ℝ n fr2) (aff_coord_pt ℝ n fr2)]
    [emetric_space (aff_coord_pt ℝ n fr2)]
    [inner_product_space K (aff_coord_vec ℝ n fr2)]
    --[semimodule ℝ (aff_coord_vec ℝ n fr1)]
   -- [semimodule ℝ (aff_coord_vec ℝ n fr2)]
    (sp1 : affine_euclidean_space ℝ n fr1)
    (sp2 : affine_euclidean_space ℝ n fr2)

  /-
  affine_coord_space_transform K n fr1 fr2 from_sp to_sp
  -/

abbreviation 
    affine_euclidean_frame_transform 
    := 
    (aff_coord_pt ℝ n fr1) 
    ≃ᵃ[ℝ] 
    (aff_coord_pt ℝ n fr2)
    
abbreviation
    affine_euclidean_space_transform
    (sp1 : affine_euclidean_space ℝ n fr1)
    (sp2 : affine_euclidean_space ℝ n fr2)
    := 
    affine_euclidean_frame_transform n fr1 fr2

attribute [reducible]
noncomputable def affine_tuple_space.to_base_euclidean_space
    (fr : affine_tuple_coord_frame ℝ n)
    : aff_trans.affine_tuple_space_transform ℝ n
    :=
    ⟨
      ⟨
        λ p ,
          ((fr.origin -ᵥ pt_zero ℝ n) : aff_vec_coord_tuple ℝ n) +ᵥ
          (⟨matrix.mul_vec 
            (affine_tuple_coord_frame.get_basis_matrix fr)
            (affine_pt_coord_tuple.to_indexed p)⟩
          : aff_pt_coord_tuple ℝ n),
        λ p,
          (vec_neg ℝ n (
                matrix.mul_vec 
                (affine_tuple_coord_frame.get_basis_matrix fr)⁻¹
                (affine_vec_coord_tuple.to_indexed 
                  ((fr.origin -ᵥ pt_zero ℝ n) : aff_vec_coord_tuple ℝ n))
          )) +ᵥ
          (⟨matrix.mul_vec 
                (affine_tuple_coord_frame.get_basis_matrix fr)⁻¹
                (↑p)⟩ : aff_pt_coord_tuple ℝ n
          ),
          sorry,
          sorry
      ⟩,
      ⟨
        λ v,
          matrix.mul_vec 
          (affine_tuple_coord_frame.get_basis_matrix fr)
          (affine_vec_coord_tuple.to_indexed v),
        sorry,
        sorry,
        λ v,
          matrix.mul_vec 
          (affine_tuple_coord_frame.get_basis_matrix fr)⁻¹
          (affine_vec_coord_tuple.to_indexed v),
        sorry,
        sorry⟩ ,
      sorry
    ⟩




attribute [reducible]
noncomputable def affine_tuple_space.to_derived_euclidean_space
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
   -- [affine_space (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n)]
    (fr : affine_tuple_coord_frame ℝ n)
    : aff_trans.affine_tuple_space_transform ℝ n
    := 
    (aff_trans.affine_tuple_space.to_base_space fr)⁻¹ 


attribute [reducible]
noncomputable def affine_tuple_space_transform.to_euclidean_transform
    (from_sp : affine_euclidean_space ℝ n fr1)
    (to_sp : affine_euclidean_space ℝ n fr2)
    (tr : aff_trans.affine_tuple_space_transform ℝ n)
    :
    affine_euclidean_space_transform n fr1 fr2 from_sp to_sp
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
  affine_euclidean_space.build_from_to_standard_transform,
  affine_euclidean_space.fold_tuple_from_to_standard_transforms
with affine_euclidean_space.build_from_to_standard_transform : 
  list (aff_fr.affine_coord_frame ℝ n) → 
                                  (affine_euclidean_space_transform n
                                      fr1
                                      (affine_coord_frame.standard ℝ n)
                                      sp1
                                      (affine_euclidean_space.mk_with_standard ℝ n))
| [] := 
  let tr := (affine_tuple_space.to_base_euclidean_space n (affine_coord_frame.get_coords fr1)) in
    affine_tuple_space_transform.to_euclidean_transform n _ _ _ _ tr
| (h::t) := 
  let tr := (affine_tuple_space.to_base_euclidean_space n (affine_coord_frame.get_coords fr1)) in 
  let trf := tr.trans (affine_euclidean_space.fold_tuple_from_to_standard_transforms t) in
    affine_tuple_space_transform.to_euclidean_transform n _ _ _ _ tr
with affine_euclidean_space.fold_tuple_from_to_standard_transforms :
  list (aff_fr.affine_coord_frame ℝ n) → 
                                  (aff_trans.affine_tuple_space_transform ℝ n)
| [] := (aff_trans.affine_tuple_space.standard_transform ℝ n )
| (h::t) := let tr := (affine_tuple_space.to_base_euclidean_space n (affine_coord_frame.get_coords fr1)) in 
      tr.trans 
          (affine_euclidean_space.fold_tuple_from_to_standard_transforms t)

attribute [reducible]
noncomputable mutual def 
  affine_euclidean_space.build_standard_to_to_transform,
  affine_euclidean_space.fold_tuple_to_to_standard_transforms
with affine_euclidean_space.build_standard_to_to_transform : 
  list (aff_fr.affine_coord_frame ℝ n) → 
                                  (affine_euclidean_space_transform n
                                      (affine_coord_frame.standard ℝ n)
                                      fr2
                                      (affine_euclidean_space.mk_with_standard ℝ n))
                                      sp2
| [] := 
  let tr := (affine_tuple_space.to_base_euclidean_space n (affine_coord_frame.get_coords fr2)) in
    ((affine_tuple_space_transform.to_euclidean_transform n fr2 (affine_coord_frame.standard ℝ n) sp2 (affine_euclidean_space.mk_with_standard ℝ n) tr).symm)
| (h::t) := 
  let tr := (aff_trans.affine_tuple_space.to_derived_space (affine_coord_frame.get_coords fr2)) in 
  let trf := tr.trans (affine_euclidean_space.fold_tuple_to_to_standard_transforms t) in
    (affine_tuple_space_transform.to_euclidean_transform n fr2 (affine_coord_frame.standard ℝ n) sp2 (affine_euclidean_space.mk_with_standard ℝ n) tr).symm
with affine_euclidean_space.fold_tuple_to_to_standard_transforms :
  list (aff_fr.affine_coord_frame ℝ n) → 
                                  (aff_trans.affine_tuple_space_transform ℝ n)
| [] := (aff_trans.affine_tuple_space.standard_transform ℝ n )
| (h::t) := 
  let tr := (aff_trans.affine_tuple_space.to_derived_space (affine_coord_frame.get_coords fr2)) in 
      tr.trans 
          (affine_euclidean_space.fold_tuple_to_to_standard_transforms t)


attribute [reducible]
noncomputable def affine_euclidean_space.build_transform
    --[inhabited (affine_coord_frame ℝ n)]
    : affine_euclidean_space_transform n fr1 fr2 sp1 sp2--affine_euclidean_space_transform n fr1 fr2 sp1 sp2
    := 
    let path := affine_coord_space.find_transform_path' sp1.1 sp2.1 in
    let from_ := (affine_euclidean_space.build_from_to_standard_transform n fr1 sp1 path.to_.tail) in
    let to_  := 
          (affine_euclidean_space.build_standard_to_to_transform n fr2 sp2 path.to_.tail) in
      ((from_.trans to_) : affine_euclidean_frame_transform n fr1 fr2)


attribute [reducible]
noncomputable def affine_tuple_basis.get_basis_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (b : affine_tuple_basis K n)
    : square_matrix K n
    :=
    λ i j,
    (aff_lib.affine_tuple_vec.get_coords  
    (
        b j))
    .nth i



attribute [reducible]
noncomputable def affine_euclidean_rotation.as_transform
    : affine_euclidean_rotation n → affine_euclidean_space_transform n fr1 fr1 sp1 sp1
| rot :=
    ⟨
      ⟨
        λ p ,
          ⟨⟨matrix.mul_vec 
          (affine_tuple_basis.get_basis_matrix rot.r)
          (↑p.1)⟩⟩,
        λ p ,
          ⟨⟨matrix.mul_vec 
          (affine_tuple_basis.get_basis_matrix rot.r)⁻¹
          (affine_pt_coord_tuple.to_indexed p.1)⟩⟩,
          sorry,
          sorry
      ⟩,
      ⟨
        λ v,
          ⟨⟨matrix.mul_vec 
          (affine_tuple_basis.get_basis_matrix rot.r)
          (affine_vec_coord_tuple.to_indexed v.1)⟩⟩
            ,
        sorry,
        sorry,
        λ v,
          ⟨⟨matrix.mul_vec 
          (affine_tuple_basis.get_basis_matrix rot.r)⁻¹
          (affine_vec_coord_tuple.to_indexed v.1)⟩⟩,
        sorry,
        sorry⟩ ,
      sorry
    ⟩

noncomputable
instance lift_rotation : has_coe
  (affine_euclidean_rotation n) 
  (affine_euclidean_space_transform n fr1 fr1 sp1 sp1) :=
  ⟨affine_euclidean_rotation.as_transform n fr1 sp1⟩
notation r`⬝`c := ↑r c

variables 
  (rot : affine_euclidean_rotation n)
  
#check (rot : affine_euclidean_space_transform n fr1 fr1 sp1 sp1).linear cv1
#check (rot : affine_euclidean_space_transform n fr1 fr1 sp1 sp1) cp1
#check rot⬝cp1 --should this work?
--#check rot cp1
end eucl_lib