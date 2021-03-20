import ..space_framed
import ..space_standard
import .measurement
import .dimension
import linear_algebra.affine_space.basic
import data.real.basic

--open framed
--open standard
open measurement

open_locale affine

namespace classical_time

variables {K : Type*} [inhabited K] [field K] --[affine_space (framed.poi)]

structure time_spc (f : fm K) extends spc K f 
structure time_point {f : fm K} (s : time_spc f) extends point K s.to_spc
structure time_vectr {f : fm K} (s : time_spc f) extends vectr K s.to_spc
-- define ops and show that this is an affine space

def std_time : time_spc (std_frame K) := ⟨std_space K⟩


variables {f : fm K} { s : time_spc f}

instance : has_add (time_vectr s) := ⟨λv1 v2, ⟨⟨⟨v1.1.1.1,v1.1.1.2,v1.coord + v2.coord⟩⟩⟩⟩
instance : has_zero (time_vectr s) := ⟨⟨⟨vec_zero K⟩⟩⟩
instance : has_neg (time_vectr s) := ⟨λv, ⟨⟨⟨v.1.1.1,v.1.1.2,-v.1.1.3⟩⟩⟩⟩

/-! ### Type class instance for abelian group -/
instance aff_comm_group_time : add_comm_group (time_vectr s) :=
sorry


/-! ### Scalar action -/


@[ext]
def vec_scalar_time : K → time_vectr s → time_vectr s :=
    λ a x, ⟨⟨⟨x.1.1.1,x.1.1.2,a*x.1.1.3⟩⟩⟩

instance : has_scalar K (time_vectr s) := ⟨vec_scalar_time⟩

instance : mul_action K (time_vectr s) := ⟨sorry, sorry⟩

instance : distrib_mul_action K (time_vectr s) := ⟨sorry,sorry⟩

instance aff_semimod_time : semimodule K (time_vectr s) := ⟨sorry, sorry⟩

instance aff_module_time : module K (time_vectr s) := ⟨sorry, sorry⟩
/-! ### group action of aff_vec_coord_tuple on aff_pt_coord_tuple -/


def aff_group_action_time : time_vectr s → time_point s → time_point s :=
    λ x y, ⟨⟨⟨y.1.1.1,y.1.1.2,x.1.1.3+y.1.1.3⟩⟩⟩


def aff_group_sub_time : time_point s → time_point s → time_vectr s :=
    λ x y, ⟨⟨⟨x.1.1.1-y.1.1.1,sorry,x.1.1.3-y.1.1.3⟩⟩⟩

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




/-
UNUSED AS OF 3/20


structure ClassicalTime {fr : fm K} extends 

  spc K fr :=
  mk::
  (id : ℕ)

structure ClassicalTimeFrame 
  {fr : fm K}
  --{sp : spc K fr} 
  (ct : @ClassicalTime K _ _ fr)
  (m : MeasurementSystem)
  :=
  mk::

structure ClassicalTimeVector
  {fr : fm K}
  {sp : spc K fr}
  {ct : ClassicalTime sp}
  {m : MeasurementSystem}
  (f : ClassicalTimeFrame ct m)
 -- (v: framed.framed_vector sp)
  extends framed.vectr sp
  :=
  mk::





structure ClassicalTimePoint
  {fr : fm K}
  {sp : spc K fr}
  {ct : ClassicalTime sp}
  {m : MeasurementSystem}
  (f : ClassicalTimeFrame ct m)
  extends framed.point sp
  :=
  mk::


variables
  {fr : fm K}
  {sp : spc K fr}
  {ct : ClassicalTime sp}
  {m : MeasurementSystem}
  {f : ClassicalTimeFrame ct m}
  (p1 : ClassicalTimeVector f)
  (p2 : ClassicalTimeVector f)

#check p1.1 +ᵥ p2.1
-/


end classical_time