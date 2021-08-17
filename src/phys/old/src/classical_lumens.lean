import .....math.affine.affine_coordinate_framed_space_lib
import .....math.affine.affine_coordinate_transform
import ..metrology.dimensions 
import ..metrology.measurement
import data.real.basic

noncomputable theory
--open real_lib
open measurementSystem
open aff_fr
open aff_lib
open aff_trans

/-
add in a frame here...measurement system attached to quantity or frame?
-/

structure classicalHertz : Type :=
mk :: 
    (sp : aff_lib.affine_coord_space.standard_space ℝ 1) 
    (id : ℕ) -- id serves as unique ID for a given geometric space


attribute [reducible]
def classicalHertz.build (id : ℕ) : classicalHertz :=
    ⟨aff_lib.affine_coord_space.mk_with_standard ℝ 1, id⟩

noncomputable def classicalHertz.algebra : classicalHertz →  
     aff_lib.affine_coord_space.standard_space ℝ 1
| (classicalHertz.mk sp n) := sp

structure classicalHertzQuantity :=
mk ::
    (sp : classicalHertz)
    (val : ℝ)

attribute [reducible]
def classicalHertzQuantity.build
    (sp : classicalHertz)
    (val : vector ℝ 1) := 
    classicalHertzQuantity.mk sp (val.nth 1)



attribute [reducible]
def classicalHertzQuantity.algebra 
    (s : classicalHertzQuantity)
    := 
    s.val

structure classicalHertzVector :=
mk ::
    (sp : classicalHertz)
    (coords : vector ℝ 1)

attribute [reducible]
def classicalHertzVector.build
    (sp : classicalHertz)
    (coords : vector ℝ 1) :=
    classicalHertzVector.mk
        sp 
        --⟨[coord], by refl⟩
        coords


attribute [reducible]
def classicalHertzVector.algebra 
    (v : classicalHertzVector)
    := 
        (aff_lib.affine_coord_space.mk_coord_vec
        (classicalHertz.algebra v.sp) 
        v.coords)


abbreviation classicalHertzBasis :=
    (fin 1) → classicalHertzVector

