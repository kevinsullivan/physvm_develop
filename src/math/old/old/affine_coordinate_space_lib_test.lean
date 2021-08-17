import data.real.basic
import .affine_coordinate_space_lib
import .real_affine_coordinate_space_lib

noncomputable theory

open aff_lib

def Rn := aff_lib.affine_coord_nspace.mk_with_standard_frame ℝ 3

def Rn_pt1 := aff_lib.affine_coord_nspace.mk_point Rn [0,0,0]
def Rn_vec1 := aff_lib.affine_coord_nspace.mk_vec Rn [1,0,0]
def Rn_vec2 := aff_lib.affine_coord_nspace.mk_vec Rn [0,1,0]
def Rn_vec3 := aff_lib.affine_coord_nspace.mk_vec Rn [0,0,1]

def origin : _ := affine_coord_nspace.origin Rn

-- TO DO NEXT
-- def frame : _ := affine_coord_nspace.frame Rn
-- def origin : _ := frame.origin --Rn

#check origin
def basis := affine_coord_nspace.basis Rn
/-

def vecsub := r3_der2_vec1 - r3_der2_vec2 -- expected :pass
def vecptadd := r3_der2_pt1 +ᵥ r3_der2_vec2 --expected : pass
def ptvecadd := r3_der2_vec2 +ᵥ r3_der2_pt1 --expected : pass
def vecptsub := r3_der2_pt1 -ᵥ r3_der2_vec2 --expected : pass
def ptvecsub := r3_der2_vec2 -ᵥ r3_der2_pt1 -- expected : pass
def pt_sub := r3_der2_pt1 - r3_der2_pt1 -- expected : pass
def pt_add := r3_der2_pt1 + r3_der2_pt1 -- expected : fail
def dif_fr := r3_der1_vec1 - r3_der2_vec2 -- expected : fail

-/
#check origin
#check basis 1 -ᵥ basis 2 --expected : pass
#check basis 1 +ᵥ basis 2 --expected : pass
#check origin +ᵥ origin --expected : fail
#check origin -ᵥ origin --expected : pass
#check basis 1 
#check basis 1 -ᵥ origin --expected : fail
#check origin -ᵥ basis 2 --expected : pass?
#check origin +ᵥ basis 2 --expected : pass



def Rn_pt1' := aff_lib.affine_coord_nspace.mk_point Rn [1,1,1]
def Rn_vec1' := aff_lib.affine_coord_nspace.mk_vec Rn [2,0,0]
def Rn_vec2' := aff_lib.affine_coord_nspace.mk_vec Rn [0,2,0]
def Rn_vec3' := aff_lib.affine_coord_nspace.mk_vec Rn [0,0,2]
--combine derived frame func into mk derived space

def der_fr := affine_coord_nspace.mk_derived_frame Rn Rn_pt1' (λ i : fin 3, match i.1 with
| 1 := Rn_vec1'
| 2 := Rn_vec2'
| 3 := Rn_vec3'
end)



def der_sp := affine_coord_nspace.mk_derived Rn der_fr

def der_origin := affine_coord_nspace.origin der_sp
def der_basis := affine_coord_nspace.basis der_sp

#check der_basis 1 +ᵥ basis 2
#check der_basis 2 +ᵥ der_basis 2
#check der_basis 1 -ᵥ basis 1
#check der_origin -ᵥ der_origin
#check der_origin -ᵥ origin

open real_lib

def R3 := real_affine_coord_nspace.mk_with_standard_frame 3