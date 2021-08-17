import .expressions.bool_expr
import .expressions.time_series.geom3d_expr
import .expressions.geom1d_expr
import .expressions.geom3d_expr
import .expressions.time_expr


open lang.time
open lang.geom1d
open lang.geom3d
open lang.series.geom3d
open lang.bool_expr

#check time

structure constrained (T : Type 1) (P : T → Prop) := 
	(val : T)
	(holds : P val)
	(fails : ¬P val)

@[class]
structure has_norm_constraint (T : Type*) := 
  (to_norm_constraint : scalar_expr → T → Prop)
notation `norm<`s := has_norm_constraint.to_norm_constraint s

instance {tf : time_frame_expr} {ts : time_space_expr tf} : has_norm_constraint (duration_expr ts) := ⟨λs, λd, ∥d.value.to_vectr∥ < s.value⟩

@[class]
structure has_time_range_constraint (T : Type*) :=
  (to_range_constraint : scalar_expr → scalar_expr → T → Prop)
notation `time ``range `x` to `y := has_time_range_constraint.to_range_constraint x y

instance {tf : time_frame_expr} {ts : time_space_expr tf} : has_time_range_constraint (time_expr ts) 
  := ⟨λs1 s2, λt, t.value.coord > s1.value ∧ t.value.coord < s2.value⟩

instance  {tf : time_frame_expr} {ts : time_space_expr tf}
	{gf : geom3d_frame_expr } {gs : geom3d_space_expr gf} : has_time_range_constraint (timestamped_pose3d_expr ts gs) 
  := ⟨λs1 s2, λt, t.value.timestamp.coord > s1.value ∧ t.value.timestamp.coord < s2.value⟩

instance  {tf : time_frame_expr} {ts : time_space_expr tf}
	{gf : geom3d_frame_expr } {gs : geom3d_space_expr gf} : has_time_range_constraint (pose3d_series_expr ts gs) 
  := ⟨λs1 s2, λte, ∀t : time ts.value, t∈te.value.domain → t.coord > s1.value ∧ t.coord < s2.value⟩



/-
def time_expr.range_constraint {tf : time_frame_expr} {ts : time_space_expr tf}
	(te : time_expr ts) : scalar → scalar → Prop 
	:= λs1 s2, te.value.coord > s1 ∧ te.value.coord < s2

def timestamped_pose3d_expr.range_constraint {tf : time_frame_expr} {ts : time_space_expr tf}
	{gf : geom3d_frame_expr } {gs : geom3d_space_expr gf}
	(s1 s2 : scalar) : timestamped_pose3d_expr ts gs → Prop 
	:= λts, ts.value.timestamp.coord > s1 ∧ ts.value.timestamp.coord < s2

def timestamped_pose3d_expr.range_constraint {tf : time_frame_expr} {ts : time_space_expr tf}
	{gf : geom3d_frame_expr } {gs : geom3d_space_expr gf}
	(s1 s2 : scalar) : timestamped_pose3d_expr ts gs → Prop 
	:= λts, ts.value.timestamp.coord > s1 ∧ ts.value.timestamp.coord < s2
def pose3d_series_expr.range_constraint {tf : time_frame_expr} {ts : time_space_expr tf}
	{gf : geom3d_frame_expr } {gs : geom3d_space_expr gf}
	(s1 s2 : scalar) : pose3d_series_expr ts gs → Prop 
	:= λte, ∀t : time ts.value, t∈te.value.domain → t.coord > s1 ∧ t.coord < s2
	-/