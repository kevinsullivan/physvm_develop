import .affine.space_standard
import .dimension
import linear_algebra.affine_space.basic

namespace time

open_locale affine

variables {K : Type*} [inhabited K] [field K] --[affine_space (framed.poi)]

-- physical space

-- 

structure time_spc (f : fm K) extends spc K f 
structure time_point {f : fm K} (s : time_spc f) extends point K s.to_spc
structure time_vectr {f : fm K} (s : time_spc f) extends vectr K s.to_spc
-- define ops and show that this is an affine space

def std_time : time_spc (std_frame K) := ⟨std_space K⟩


variables {f : fm K} { s : time_spc f}

instance : has_add (time_vectr s) := ⟨λv1 v2, ⟨v1.to_vectr +ᵥ v2.to_vectr⟩⟩--⟨⟨⟨(v1.to_vectr.to_vec.fst,v1.to_vectr.to_vec.coords + v2.to_vectr.to_vec.coords), v1.to_vectr.to_vec.pf⟩⟩⟩⟩
instance : has_zero (time_vectr s) := ⟨⟨⟨vec_zero K⟩⟩⟩
instance : has_neg (time_vectr s) := ⟨λv, ⟨-v.to_vectr⟩⟩

/-! ### Type class instance for abelian group -/
instance aff_comm_group_time : add_comm_group (time_vectr s) :=
sorry


/-! ### Scalar action -/


@[ext]
def vec_scalar_time : K → time_vectr s → time_vectr s :=
    λ a x, ⟨a•x.to_vectr⟩
instance : has_scalar K (time_vectr s) := ⟨vec_scalar_time⟩

instance : mul_action K (time_vectr s) := ⟨sorry, sorry⟩

instance : distrib_mul_action K (time_vectr s) := ⟨sorry,sorry⟩

instance aff_semimod_time : semimodule K (time_vectr s) := ⟨sorry, sorry⟩

instance aff_module_time : module K (time_vectr s) := ⟨sorry, sorry⟩
/-! ### group action of aff_vec_coord_tuple on aff_pt_coord_tuple -/


def aff_group_action_time : time_vectr s → time_point s → time_point s :=
    λ x y, ⟨x.to_vectr +ᵥ y.to_point⟩

def aff_group_sub_time : time_point s → time_point s → time_vectr s :=
    λ x y, ⟨x.to_point -ᵥ y.to_point⟩
#check add_action

instance : has_vadd (time_vectr s) (time_point s) := ⟨aff_group_action_time⟩

instance : has_vsub (time_vectr s) (time_point s) := ⟨aff_group_sub_time⟩

instance : add_action (time_vectr s) (time_point s) := ⟨
    aff_group_action_time, 
    sorry, 
    sorry⟩


instance : nonempty (time_point s) := ⟨⟨⟨pt_zero K⟩⟩⟩

instance aff_torsor_time : add_torsor (time_vectr s) (time_point s) := 
⟨sorry,
sorry,
sorry,
sorry,
sorry,
sorry⟩


instance aff_coord_is_time : 
    affine_space
        (time_vectr s) 
        (time_point s) := 
    ⟨sorry,
sorry,
sorry,
sorry,
sorry,
sorry⟩


end time