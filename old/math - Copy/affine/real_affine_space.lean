import .affine_coordinate_space
import .affine_coordinate_basis
import .affine_space_types
import data.real.basic


namespace real_affine

abbreviation real_vec := aff_vec_coord_tuple ℝ
abbreviation real_pt  := aff_pt_coord_tuple  ℝ

abbreviation r3_vec := real_vec 3
abbreviation r3_pt  := real_pt  3

universes u v w

open aff_fr 

#check affine_space_type

-- TODO: Fix type universes???
abbreviation real_affine_coordinate_point 
    {X : Type u} {V : Type w} (dim : ℕ) 
    [add_comm_group V] [module ℝ V] [affine_space V X] 
    := 
    pt_with_frame X ℝ V (fin dim)
    --pt_with_frame (aff_pt_coord_tuple ℝ dim) ℝ (aff_vec_coord_tuple ℝ dim) (fin dim) 

abbreviation real_affine_coordinate_vector  
    {X : Type*} {V : Type*} (dim : ℕ) 
    [add_comm_group V] [module ℝ V] [affine_space V X] 
    := 
    vec_with_frame X ℝ V (fin dim)--(dim : ℕ) := 
    --vec_with_frame (aff_pt_coord_tuple ℝ dim) ℝ (aff_vec_coord_tuple ℝ dim) (fin dim) 

abbreviation real_affine_frame 
    (X : Type*) (V : Type*) (dim : ℕ) 
    [add_comm_group V] [module ℝ V] [affine_space V X]
    :=
    affine_frame  X ℝ V (fin dim)
--abbreviation real_affine_frame (dim : ℕ) := 
    --affine_frame  (aff_pt_coord_tuple ℝ dim) ℝ (aff_vec_coord_tuple ℝ dim) (fin dim)
--    aff_fr_struct dim (aff_pt_coord_tuple ℝ dim) ℝ (aff_vec_coord_tuple ℝ dim) 
--abbreviation derived_fr {dim : ℕ} := affine_frame  (aff_pt_coord_tuple ℝ dim) ℝ (aff_vec_coord_tuple ℝ dim) (fin dim)

abbreviation real_affine_vector (dim : ℕ) :=
    (aff_vec_coord_tuple ℝ dim)

abbreviation real_affine_point (dim : ℕ) :=
    (aff_pt_coord_tuple ℝ dim)


abbreviation real_affine_coordinate_space {X : Type*} {V : Type*}  {dim : ℕ}
    [add_comm_group V] [module ℝ V] [affine_space V X]
    (fr : affine_frame  X ℝ V (fin dim)) 
    :=
     affine_space_type dim (real_affine_coordinate_point dim fr) ℝ (real_affine_coordinate_vector dim fr)
    --affine_space_type dim X ℝ V
-- This is still needed
-- Basically an abbreviation
--def real_affine_space (dim : ℕ) := 
--    affine_space_type dim (aff_pt_coord_tuple ℝ dim) ℝ (aff_vec_coord_tuple ℝ dim)

def real_affine_coordinate_space.get_coordinate_frame {X : Type*} {V : Type*}
    [add_comm_group V] [module ℝ V] [affine_space V X]{dim : ℕ}  
    {f : real_affine_frame X V dim} 
    (sp : real_affine_coordinate_space f)
    : real_affine_frame X V dim 
:= f

def real_affine_coordinate_space.get_derived_frame {X : Type*} {V : Type*}
    [add_comm_group V] [module ℝ V] [affine_space V X]{dim : ℕ} 
    {f : real_affine_frame X V dim}
    (original :affine_space_type dim (real_affine_coordinate_point dim f) ℝ (real_affine_coordinate_vector dim f))
    (origin : (real_affine_coordinate_point dim f)) 
    (basis : fin dim → (real_affine_coordinate_vector dim f) )
    : affine_frame (real_affine_coordinate_point dim f) ℝ (real_affine_coordinate_vector dim f) (fin dim) 
    :=
    (⟨origin, basis, sorry⟩ : affine_frame (real_affine_coordinate_point dim f) ℝ (real_affine_coordinate_vector dim f) (fin dim))


def real_affine_coordinate_spaces.change_coordinate_space  {X : Type*} {V : Type*}
    [add_comm_group V] [module ℝ V] [affine_space V X]{dim : ℕ} 
    {f : real_affine_frame X V dim}
    (original :affine_space_type dim (real_affine_coordinate_point dim f) ℝ (real_affine_coordinate_vector dim f))
    (origin : (real_affine_coordinate_point dim f)) 
    (basis : fin dim → (real_affine_coordinate_vector dim f) )
    : real_affine_coordinate_space (real_affine_coordinate_space.get_derived_frame original origin basis) 
    :=
    let fr :  affine_frame (real_affine_coordinate_point dim f) ℝ (real_affine_coordinate_vector dim f) (fin dim) 
        := (real_affine_coordinate_space.get_derived_frame original origin basis) in
    (⟨⟩ : real_affine_coordinate_space fr)

    
    --real_affine_coordinate_space 
    --    (affine_frame.mk
    --        (aff_pt_coord_tuple.mk (vector_to_pt_list origin) sorry sorry)
    --         (λ x: fin dim, ⟨vector_to_vec_list (basis x),sorry,sorry⟩) sorry )

noncomputable def to_affine_space -- {X : Type*} {V : Type*}
    --[add_comm_group V] [module ℝ V] [affine_space V X]{dim : ℕ}  
     (dim : ℕ) : 
    real_affine_coordinate_space 
        (aff_basis.std_frame ℝ dim : real_affine_frame (aff_pt_coord_tuple ℝ dim) (aff_vec_coord_tuple ℝ dim) dim)
        --(⟨⟩ : affine_space_type dim (aff_pt_coord_tuple ℝ dim) ℝ (aff_vec_coord_tuple ℝ dim))
        :=
        ⟨⟩
 

end real_affine