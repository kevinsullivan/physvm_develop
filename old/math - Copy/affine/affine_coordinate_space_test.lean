--import .affine_coordinate_space
import data.real.basic
import .affine_coordinate_frame

/-
Real affine coordinate 3 space.
-/

def real_affine_3_space := affine_coord_space_type ℝ (3 : ℕ) 

def real_affine_3_space_1: real_affine_3_space := ⟨⟩ 
def real_affine_3_space_2: real_affine_3_space := ⟨⟩ 

example : real_affine_3_space_1 = real_affine_3_space_2 := rfl


noncomputable def real_affine_3_standard_frame : _ := aff_basis.aff_coord_space_std_frame ℝ 3

#check real_affine_3_standard_frame
/-
We've managed to define a real affine 3 space and a standard frame,
but the frame isn't yet "a part of" such a space.
-/