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

structure classicalLuminousIntensity : Type :=
mk :: 
    (sp : aff_lib.affine_coord_space.standard_space ℝ 1) 
    (id : ℕ) -- id serves as unique ID for a given geometric space


attribute [reducible]
def classicalLuminousIntensity.build (id : ℕ) : classicalLuminousIntensity :=
    ⟨aff_lib.affine_coord_space.mk_with_standard ℝ 1, id⟩

noncomputable def classicalLuminousIntensity.algebra : classicalLuminousIntensity →  
     aff_lib.affine_coord_space.standard_space ℝ 1
| (classicalLuminousIntensity.mk sp n) := sp

structure classicalLuminousIntensityQuantity :=
mk ::
    (sp : classicalLuminousIntensity)
    (val : ℝ)

attribute [reducible]
def classicalLuminousIntensityQuantity.build
    (sp : classicalLuminousIntensity)
    (val : vector ℝ 1) := 
    classicalLuminousIntensityQuantity.mk sp (val.nth 1)



attribute [reducible]
def classicalLuminousIntensityQuantity.algebra 
    (s : classicalLuminousIntensityQuantity)
    := 
    s.val

/-
no need for a vector? no notion of luminous intensity vector?
-/
/-
structure classicalLuminousIntensityVector :=
mk ::
    (sp : classicalLuminousIntensity)
    (coords : vector ℝ 1)

attribute [reducible]
def classicalLuminousIntensityVector.build
    (sp : classicalLuminousIntensity)
    (coords : vector ℝ 1) :=
    classicalLuminousIntensityVector.mk
        sp 
        --⟨[coord], by refl⟩
        coords


attribute [reducible]
def classicalLuminousIntensityVector.algebra 
    (v : classicalLuminousIntensityVector)
    := 
        (aff_lib.affine_coord_space.mk_coord_vec
        (classicalLuminousIntensity.algebra v.sp) 
        v.coords)


abbreviation classicalLuminousIntensityBasis :=
    (fin 1) → classicalLuminousIntensityVector
-/
