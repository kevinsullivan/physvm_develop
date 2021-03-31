import ..expressions.time_expr



open lang.time

--alias std frame and space up here
def fr := (std_frame ℚ TIME)
def sp :=  (std_space ℚ TIME)


def launch_time := time_expr.lit (mk_time sp 0)
def one_second := duration_expr.lit (mk_duration sp 1)

/-
Using transform requires adding in a second space argument for right now. This is "very bad" for us. 

Use env and eval to extract literals to construct new frames and spaces, etc
-/

def env_ := @env.init ℚ _ _ fr sp fr sp
def eval_ := @eval.init ℚ _ _ fr sp fr sp

def time_frame  := mk_frame (eval_.t env_.t launch_time).to_point (eval_.d env_.d one_second).to_vectr
def mission_time  := mk_space ℚ (time_frame)

def env_m := @env.init ℚ _ _ time_frame mission_time time_frame mission_time
def eval_m := @eval.init ℚ _ _ time_frame mission_time time_frame mission_time


def ego_launch_time     := time_expr.lit (mk_time mission_time 0)
def t_plus_one_minute   := mk_time mission_time 60
def one_minute          := duration_expr.lit (mk_duration mission_time 60)
def t_plus_one_minute'  := one_minute +ᵥ ego_launch_time     -- coordinate free in coordinate space
def t_plus_one_second   := one_second +ᵥ ego_launch_time     -- frame error

def env_tr := @env.init ℚ _ _ fr sp time_frame mission_time
def eval_tr := @eval.init ℚ _ _ fr sp time_frame mission_time

--build a transform
def std_to_mission :=       transform_expr.lit ⟨(spc.time_tr ℚ sp mission_time)⟩

--transform original launch_time point in std_space to mission space
def launch_time_in_time_frame := 
  let std_to_mission_lit :=   eval_tr.tr env_tr.tr std_to_mission in
  let launch_time_lit :=      eval_.t env_.t launch_time in
  std_to_mission_lit.to_equiv launch_time_lit