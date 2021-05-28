import .framed_affine_space
import .affine_coordinate_frame
import data.real.basic
--import .affine_coordinate_space_test
open aff_fr
noncomputable theory

def real_affine_3_standard_frame 
    : _ := aff_basis.aff_coord_space_std_frame 

def real_affine3_std_frame := aff_basis.aff_coord_space_std_frame ℝ 3

def sp : framed_affine_coord_space_type 
    (aff_pt_coord_tuple ℝ 3) (aff_vec_coord_tuple ℝ 3) ℝ 3 real_affine3_std_frame
    := ⟨⟩

def std_pt_type := (pt_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame)

def std_vec_type := 
    (vec_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame)
/-

instance : add_comm_group (vec_with_frame X K V ι basis) :=
⟨
  vecf_add X K V ι basis, 
  vadd_assoc X K V ι basis, 
  vecf_zero X K V ι basis, 
  vzero_add X K V ι basis, 
  vadd_zero X K V ι basis, 
  vecf_neg X K V ι basis,
  vadd_left_neg X K V ι basis,
  vadd_comm X K V ι basis
⟩

why won't this recognize add_comm_group??

-/


def pt_origin : 
    (pt_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame)
    := ⟨⟨[1,0,0,0],sorry,sorry⟩⟩
def vec_basis1 : 
    (vec_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame)
    := ⟨⟨[0,1,0,0],sorry,sorry⟩⟩
def vec_basis2 : 
    (vec_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame)
    := ⟨⟨[0,0,1,0],sorry,sorry⟩⟩
def vec_basis3 : 
    (vec_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame)
    := ⟨⟨[0,0,0,1],sorry,sorry⟩⟩

universes u v w
abbreviation pt_wrapper {X : Type u} {K : Type v} {V : Type w}
[inhabited K] [field K] [add_comm_group V] [vector_space K V] [affine_space V X]
(fr : affine_frame X K V (fin 3))
:= pt_with_frame X K V (fin 3) fr
abbreviation vec_wrapper {X : Type u} {K : Type v} {V : Type w}
[inhabited K] [field K] [add_comm_group V] [vector_space K V] [affine_space V X]
(fr : affine_frame X K V (fin 3))
:= vec_with_frame X K V (fin 3) fr

/-
def derived_frame : affine_frame (pt_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) ℝ (vec_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) (fin 3):= 
        ⟨pt_origin, λi:fin 3, 
            if i = 1 then vec_basis1 
            else (if i = 2 then vec_basis2 else vec_basis3), sorry⟩

def derived_space : framed_affine_coord_space_type 
(pt_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame)
(vec_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame)
ℝ 3 derived_frame := ⟨ ⟩ -/
 /--/   (pt_with_frame (pt_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) ℝ (vec_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) (fin 3) derived_frame) 
        ℝ 
        (vec_with_frame (pt_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) ℝ (vec_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) (fin 3) derived_frame)
-/
def derived_frame : affine_frame (pt_wrapper 
        real_affine3_std_frame) ℝ (vec_wrapper 
        real_affine3_std_frame) (fin 3)   := 
        ⟨pt_origin, λi:fin 3, 
            if i = 1 then vec_basis1 
            else (if i = 2 then vec_basis2 else vec_basis3), sorry⟩

def derived_space : framed_affine_coord_space_type 
(pt_wrapper 
        real_affine3_std_frame) 
(vec_wrapper 
        real_affine3_std_frame)
ℝ 3 derived_frame := ⟨ ⟩

/-
def pt_origin_derived : 
    pt_with_frame (pt_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) ℝ (vec_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) (fin 3) derived_frame :=
        ⟨pt_origin⟩


def vec_basis1_derived : 
    vec_with_frame (pt_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) ℝ (vec_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) (fin 3) derived_frame :=
        ⟨vec_basis3⟩
        

def vec_basis2_derived : 
    vec_with_frame (pt_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) ℝ (vec_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) (fin 3) derived_frame :=
        ⟨vec_basis1⟩
        

def vec_basis3_derived : 
    vec_with_frame (pt_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) ℝ (vec_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) (fin 3) derived_frame :=
        ⟨vec_basis2⟩-/
def pt_origin_derived :
    pt_with_frame 
        (pt_wrapper real_affine3_std_frame) ℝ 
        (vec_wrapper real_affine3_std_frame) (fin 3) derived_frame :=
        ⟨pt_origin⟩


def vec_basis1_derived : 
    vec_with_frame 
        (pt_wrapper real_affine3_std_frame) ℝ 
        (vec_wrapper real_affine3_std_frame) (fin 3) derived_frame :=
        ⟨vec_basis3⟩
        

def vec_basis2_derived : 
    vec_with_frame 
        (pt_wrapper real_affine3_std_frame) ℝ 
        (vec_wrapper real_affine3_std_frame) (fin 3) derived_frame :=
        ⟨vec_basis1⟩
        

def vec_basis3_derived : 
    vec_with_frame 
        (pt_wrapper real_affine3_std_frame) ℝ 
        (vec_wrapper real_affine3_std_frame) (fin 3) derived_frame :=
        ⟨vec_basis2⟩

/-
def derived_frame2 : affine_frame 
        (pt_with_frame (pt_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) ℝ (vec_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) (fin 3) derived_frame) 
        ℝ 
        (vec_with_frame (pt_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) ℝ (vec_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) (fin 3) derived_frame)
        (fin 3) :=
        ⟨pt_origin_derived, λi:fin 3, 
            if i = 1 then vec_basis1_derived 
            else (if i = 2 then vec_basis2_derived else vec_basis3_derived), sorry⟩
-/
def derived_frame2 : affine_frame 
        (pt_wrapper derived_frame)
        ℝ 
        (vec_wrapper derived_frame)
        (fin 3) :=
        ⟨pt_origin_derived, λi:fin 3, 
            if i = 1 then vec_basis1_derived 
            else (if i = 2 then vec_basis2_derived else vec_basis3_derived), sorry⟩
/-
def derived_space2 : framed_affine_coord_space_type
(pt_with_frame (pt_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) ℝ (vec_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) (fin 3) derived_frame)
(vec_with_frame (pt_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) ℝ (vec_with_frame 
        (aff_pt_coord_tuple ℝ 3) ℝ (aff_vec_coord_tuple ℝ 3) (fin 3) 
        real_affine3_std_frame) (fin 3) derived_frame)
ℝ 3 derived_frame2 := ⟨⟩
-/
def derived_space2 : framed_affine_coord_space_type
(pt_wrapper derived_frame)
(vec_wrapper derived_frame)
ℝ 3 derived_frame2 := ⟨⟩

--no way to get a standard frame on derived spaces deductively
--possible to push it up inductively

def derived_std_frame_origin : (pt_wrapper derived_frame) :=
    ⟨⟨real_affine3_std_frame.origin⟩⟩
def derived_std_frame_basis : fin 3 → vec_wrapper derived_frame :=
    (λ i : fin 3,
        ⟨⟨real_affine3_std_frame.vec i⟩⟩)


def derived_sp_std_frame :
    affine_frame 
        (pt_wrapper derived_frame)
        ℝ 
        (vec_wrapper derived_frame)
        (fin 3)
    := ⟨derived_std_frame_origin,derived_std_frame_basis,sorry⟩ 