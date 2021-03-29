import ..environment.environment_with_assign

universes u

variables (K : Type u) [field K] [inhabited K] {f : fm K} {sp : spc K f} 

inductive cmd : Type u
| skip 
| assign_spc (v : lang.math.sp_var f) (sp : lang.math.sp_expr f)
| assign_fm (v : lang.math.fm_var) (f : lang.math.fm_expr K)
| assign_duration (v : lang.time.duration_var sp) (d : lang.time.duration_expr sp)
| assign_time (v : lang.time.time_var sp) (t : lang.time.time_expr sp)

def cmd_eval : env.env K → @cmd K _ _ f sp → @env.env K _ _ f sp
| e (cmd.skip) := e
| i (cmd.assign_spc v e) := assign_spc sp i v e
| i (cmd.assign_fm v e) := @assign_fm K _ _ f sp i v e
| i (cmd.assign_duration v e) := assign_duration sp i v e
| i (cmd.assign_time v e) := assign_time sp i v e

/-import ..environment.environment_with_assign

universes u

variables (K : Type u) [field K] [inhabited K] {f : fm K} {sp : spc K f} 

inductive cmd : Type u
| skip 
| assign_spc (v : lang.math.sp_var f) (sp : lang.math.sp_expr f)
| assign_fm (v : lang.math.fm_var) (f : lang.math.fm_expr K)
| assign_duration (v : lang.time.duration_var) (d : lang.time.duration_expr sp)
| assign_time (v : lang.time.time_var) (t : @lang.time.time_expr K _ _ f sp)

def cmdEval : @env.env K _ _ f sp → @cmd K _ _ f sp → @env.env K _ _ f sp
| e (cmd.skip) := e
| i (cmd.assign_spc v e) := @assign_spc K _ _ f sp i v e
| i (cmd.assign_fm v e) := @assign_fm K _ _ f sp i v e
| i (cmd.assign_duration v e) := @assign_duration K _ _ f sp i v e
| i (cmd.assign_time v e) := @assign_time K _ _ f sp i v e
-/