import ..expressions.time_expr2

/-
Adapted from Dr Sullivan's phys/demo/demo.lean to highlight differences from phys and lang
-/

open lang.time

--Alias std time frame and space
def std_fr := (std_frame ℚ TIME)
def std_sp :=  (std_space ℚ TIME)

/-
Define a time and duration expression constructed from phys literals
-/
def launch_time : time_expr std_sp := (time_expr.lit (mk_time std_sp 0))
def one_second : duration_expr std_sp := duration_expr.lit (mk_duration std_sp 1)

/-
Use env and eval to extract literals to construct new frames and spaces, etc

No space argument is provided anymore, but you need to provide the environment with types
to specify exactly what you expect to receive from it. Can make these implicit, but as shown below,
can we assume they can be provided by context?
-/
def env_ := env.init ℚ 
def eval_ := eval.init ℚ 

/-
Construct a new frame, based on the standard frame,
using the prior time and duration
-/
def time_frame  := 
    let time_sp_eval := eval_.t std_sp in --As shown here, index into the evaluation and env
    let time_sp_env := env_.t std_sp in   --functions to indicate what data type you expect the env/eval to return
    let dur_sp_eval := eval_.d std_sp in
    let dur_sp_env := env_.d std_sp in
    mk_frame (time_sp_eval time_sp_env launch_time).to_point (dur_sp_eval dur_sp_env one_second).to_vectr

/-
Construct a new space with this frame
-/
def mission_time  := mk_space ℚ (time_frame)

/-
Define new times and durations in terms of this new frame,
demonstrate 
-/
def ego_launch_time     := time_expr.lit (mk_time mission_time 0)
def t_plus_one_minute   := mk_time mission_time 60
def one_minute          := duration_expr.lit (mk_duration mission_time 60)
def t_plus_one_minute'  := one_minute +ᵥ ego_launch_time     -- coordinate free in coordinate space
def t_plus_one_second   := one_second +ᵥ ego_launch_time     -- frame error

--build a transform
def std_to_mission :=       transform_expr.lit (std_sp.time_tr mission_time)

--transform original launch_time point in std_space to mission space
def launch_time_in_time_frame := 
  let std_to_mission_lit :=   (eval_.tr std_sp mission_time) (env_.tr std_sp mission_time) std_to_mission in
  let launch_time_lit :=      (eval_.t std_sp) (env_.t std_sp) launch_time in
    std_to_mission_lit.transform_time launch_time_lit