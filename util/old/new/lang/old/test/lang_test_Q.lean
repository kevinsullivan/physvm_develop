import ..imperative_DSL.physlang

#check 1

/-
uncertain how this should get printed
-/


abbreviation K := ℚ
/-
If we want to include in a different space, whether it be a 2nd time or geom, 
problems come up here. Either we share the same space in the environment, 
or we add in new space type arguments to env. This does not appear to scale to a user
creating arbitrary frames or spaces.
-/
def env1 : @env.env K _ _ (std_frame K TIME) (std_space K TIME) := env.env.init K

--Bind a time object to variable and in environment
def assign_t1 :=
  cmd.assign_time ⟨⟨"t1"⟩⟩ (lang.time.time_expr.lit (mk_time (std_space K TIME) 5 ))
def env2 := cmd_eval K env1 assign_t1

--Bind a time object to variable and in environment
def assign_t2 :=
  cmd.assign_time ⟨⟨"t2"⟩⟩ (lang.time.time_expr.var (⟨⟨"t1"⟩⟩ : lang.time.time_var (std_space K TIME)))
def env3 := cmd_eval K env2 assign_t2

--When it is computable, we have access to the coordinates just fine.
#eval (lang.time_eval.time_eval (std_space K TIME) env3.t (lang.time.time_expr.var (⟨⟨"t1"⟩⟩ : lang.time.time_var (std_space K TIME))))
  .to_point.to_pt.to_prod

--Bind a duration object by subtracting times (which are evaluated from variables)
def assign_d1 :=
  let eval_t1 := (lang.time_eval.time_eval (std_space K TIME) env3.t (lang.time.time_expr.var (⟨⟨"t1"⟩⟩ : lang.time.time_var (std_space K TIME)))) in
  let eval_t2 := (lang.time_eval.time_eval (std_space K TIME) env3.t (lang.time.time_expr.var (⟨⟨"t2"⟩⟩ : lang.time.time_var (std_space K TIME)))) in
  cmd.assign_duration ⟨⟨"d1"⟩⟩ (lang.time.duration_expr.lit (
    eval_t1
    -ᵥ
    eval_t2
  ))

def env4 := cmd_eval K env3 assign_d1

def assign_robot_frame :=
  let eval_t1 := (lang.time_eval.time_eval (std_space K TIME) env3.t (lang.time.time_expr.var (⟨⟨"t1"⟩⟩ : lang.time.time_var (std_space K TIME)))) in
  let eval_d1 := (lang.time_eval.duration_eval (std_space K TIME) env3.t (lang.time.duration_expr.var (⟨⟨"d1"⟩⟩ : lang.time.duration_var (std_space K TIME)))) in
  --starts getting ugly - cmd needs some explicit arguments, which hardly make sense
  --@cmd.assign_fm K _ _ (std_frame K TIME) (std_space K TIME)
  @cmd.assign_fm K _ _ (std_frame K TIME) (std_space K TIME) ⟨⟨"robot"⟩⟩ (lang.math.fm_expr.lit (mk_frame eval_t1.to_point eval_d1.to_vectr))

def env5 := cmd_eval K env4 assign_robot_frame

def assign_robot_space :=
  let eval_robot := (lang.math_eval.fm_eval (std_frame K TIME)/-<-what is this doing here-/ 
    env4.m (lang.math.fm_expr.var (⟨⟨"robot"⟩⟩))) in
  --@cmd.assign_spc K _ _ (std_frame K TIME) (std_space K TIME) ⟨⟨"robot"⟩⟩ (mk_space K eval_robot) 
  --odd but functional.
  @cmd.assign_spc K _ _ (eval_robot) (mk_space K eval_robot) ⟨⟨"robot"⟩⟩ (lang.math.sp_expr.lit (mk_space K eval_robot))


def env6 := cmd_eval K env5 /-and then...-/ assign_robot_space
/-
This is where things break down because, as mentioned above, environment only supports 1 frame due to the necessary implicit arguments
How to fix this (just at the lang level) is something I don't have a quick answer for. 
-/