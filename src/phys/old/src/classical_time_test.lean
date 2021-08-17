import .classical_time

/-
Instantiate two different physical time spaces,
to test that our design meets the requirement we
set out in the README file. Two unrelated spaces
modeling separate timelines.
-/
noncomputable def timeline1 := classicalTime.mk 0
noncomputable def timeline2 := classicalTime.mk 0

/-
Get the underlying affine space for each of these 
timelines.
-/

def timeline1_space : real_affine.Algebra := 
    classicalTimeAlgebra timeline1

def timeline2_space : real_affine.Algebra := 
    classicalTimeAlgebra timeline2

/-
structure affine_space_type  -- parameterized affine space type
    (dim : ℕ)
    (X : Type u)
    (K : Type v)
    (V : Type w)
    [ring K] 
    [add_comm_group V] 
    [module K V]  
    [affine_space V X]

-- real affine space type parameterized by dimension
def real_affine_space (dim : ℕ) : := 
    affine_space_type dim (aff_pt_coord_tuple ℝ dim) ℝ (aff_vec_coord_tuple ℝ dim)

-- AFFINE COORDINATE SPACES

-- The type of affine vector coordinate tuples
@[ext]
structure aff_vec_coord_tuple :=
(l : list k)
(len_fixed : l.length = n + 1)
(fst_zero : head l = 0)

-- The type of affine point coordinate tuples
@[ext]
structure aff_pt_coord_tuple :=
(l : list k)
(len_fixed : l.length = n + 1)
(fst_one : head l = 1)

-- Bottom line: such sets of coordinate tuples form affine spaces
instance aff_coord_is : affine_space (aff_vec_coord_tuple k n) (aff_pt_coord_tuple k n) := aff_torsor k n




Definition 1 : 
affine_with_frame

inductive affine_frame --need proof that "standard" is THE standard basis?
| standard (ref_pt : X) (vec : ι → V) (basis : is_basis K vec ) : affine_frame
| derived (ref_pt : X) (vec : ι → V) (basis :  is_basis K vec ) : affine_frame → affine_frame

@[ext]
structure vec_with_frame (frame : affine_frame X K V ι) :=
(vec : V)

structure pt_with_frame (frame : affine_frame X K V ι) :=
(pt : X)

instance : affine_space (vec_with_frame X K V ι basis) (pt_with_frame X K V ι basis) := sorry


-----------------------

inductive Algebra  
| aff_space 
    {dim : ℕ} {X : Type} {K : Type} {V : Type} 
    [ring K] 
    [add_comm_group V] 
    [module K V]  
    [affine_space V X] 
    (a : affine_space_type dim X K V)

!!!
abbreviation real_coordinatized_affine_space {dim : ℕ} (fr : r_fr dim) :=
     affine_space_type dim (real_affine_point_with_frame dim fr) ℝ (real_affine_vector_with_frame dim fr)

def to_affine_space (n : ℕ) : real_affine_space n :=
    ⟨⟩
    --⟨aff_pt_coord_tuple ℝ n, ℝ, aff_vec_coord_tuple ℝ n, real.ring, aff_comm_group ℝ n, aff_module ℝ n, aff_coord_is ℝ n⟩

to be deleted later following today's convo ↓ 
def to_coordinatized_affine_space (n : ℕ) (fr : r_fr n) : real_coordinatized_affine_space fr :=--(get_standard_frame_on_Rn n) := 
    ⟨⟩ --⟨real.ring, prf_real_add_comm_grp_n n,prf_vec_module_n n,prf_aff_crd_sp n, get_standard_frame n⟩


-/

-/
-- Lemma: every timeline has the same affine space
example : timeline1_space = timeline2_space := rfl


def si := measurementSystem.si_measurement_system

noncomputable def my_standard_frame := 
    classicalTimeFrame.standard timeline1 si

noncomputable def my_standard_frame_algebra := classicalTimeFrameAlgebra my_standard_frame 


noncomputable def my_vector : classicalTimeVector timeline1 :=
    classicalTimeVector.mk  1 ⟨[2],sorry⟩

noncomputable def my_vector_algebra := classicalTimeVectorAlgebra my_vector

noncomputable def std_vector : classicalTimeCoordinateVector timeline1 
    := {f:=my_standard_frame,..my_vector}
    
noncomputable def my_std_vector_algebra := classicalTimeCoordinateVectorAlgebra std_vector


noncomputable def my_Point : classicalTimePoint timeline1 :=
    classicalTimePoint.mk  1 ⟨[0],sorry⟩

noncomputable def my_point_algebra := classicalTimePoint 

noncomputable def std_point : classicalTimeCoordinatePoint timeline1 
    := {f:=my_standard_frame,..my_Point}


noncomputable def my_derived_frame : classicalTimeFrame timeline1 :=
    classicalTimeFrame.derived timeline1 my_standard_frame my_Point (λone : fin 1,my_vector) si

