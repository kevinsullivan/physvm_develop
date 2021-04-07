import ..expressions.time_expr_current

/-
Adapted from Dr Sullivan's phys/demo/demo.lean to highlight differences from phys and lang
-/

open lang.time

--Alias std time frame and space
def std_fr : time_frame_expr ℚ := [(time_std_frame ℚ)] --(std_frame ℚ TIME)
def std_sp : time_space_expr ℚ :=  [(time_std_space ℚ)] --(std_space ℚ TIME)

/-
Use env and eval to extract literals to construct new frames and spaces, etc

No space argument is provided anymore, but you need to provide the environment with types
to specify exactly what you expect to receive from it. Can make these implicit, but as shown below,
can we assume they can be provided by context?
-/
def env_ : env := env.init ℚ 
def eval_ : eval := eval.init ℚ 
/-
Use of new notation
-/
def launch_time : 
  let frame_lit := (eval_.frame_eval env_.frame_env std_fr) in
  let std_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) std_sp) in
  time_expr std_lit 
  := 
  let frame_lit := (eval_.frame_eval env_.frame_env std_fr) in
  let std_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) std_sp) in
  [(mk_time std_lit 0)]

def one_second : 
  let frame_lit := (eval_.frame_eval env_.frame_env std_fr) in
  let std_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) std_sp) in
  duration_expr std_lit 
  := 
  let frame_lit := (eval_.frame_eval env_.frame_env std_fr) in
  let std_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) std_sp) in
  [(mk_duration std_lit 1)]

-- TODO: Introduce concrete syntax notations

/-
Frame definition updated with embedding into expression
-/
def mission_frame : time_frame_expr ℚ  := 
    mk_time_frame_expr ℚ launch_time one_second
/-
Construct a new space with this frame

def mission_time := mk_space ℚ (time_frame)
-/

/-
Space definition updated with embedding into expression
-/

def mission_space : time_space_expr ℚ :=
  let frame_lit := (eval_.frame_eval env_.frame_env mission_frame) in
  [(mk_space ℚ frame_lit)]

/-
Alternative definition
-/
def mission_space' : time_space_expr ℚ :=
  mk_time_space_expr ℚ mission_frame
def mission_space'' : time_space_expr ℚ :=
  time_space_expr.mk mission_frame--mk_time_space_expr ℚ mission_frame

/-

-/



/-
Define new times and durations in terms of this new frame,
demonstrate 
-/

def ego_launch_time : 
  let frame_lit := (eval_.frame_eval env_.frame_env mission_frame) in
  let mission_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) mission_space) in
  time_expr mission_lit  
  :=
  let frame_lit := (eval_.frame_eval env_.frame_env mission_frame) in
  let mission_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) mission_space) in 
  time_expr.lit (mk_time mission_lit 0)

def one_minute : 
  let frame_lit := (eval_.frame_eval env_.frame_env mission_frame) in
  let mission_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) mission_space) in
  duration_expr mission_lit 
  := 
  let frame_lit := (eval_.frame_eval env_.frame_env mission_frame) in
  let mission_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) mission_space) in
  duration_expr.lit (mk_duration mission_lit 60)

def t_plus_one_minute' : _ := 
  one_minute +ᵥ ego_launch_time     -- coordinate free in coordinate space
def t_plus_one_second : _  := one_second +ᵥ ego_launch_time     -- frame error



--build a transform
def std_to_mission : 
  let frame_lit := (eval_.frame_eval env_.frame_env std_fr) in
  let std_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) std_sp) in
  let frame_lit := (eval_.frame_eval env_.frame_env mission_frame) in
  let mission_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) mission_space) in
  transform_expr std_lit mission_lit  --type
  := 
  let frame_lit := (eval_.frame_eval env_.frame_env std_fr) in
  let std_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) std_sp) in
  let frame_lit := (eval_.frame_eval env_.frame_env mission_frame) in
  let mission_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) mission_space) in      
  transform_expr.lit (std_lit.time_tr mission_lit) --value

--transform original launch_time point in std_space to mission space
def launch_time_in_time_frame : 
  let frame_lit := (eval_.frame_eval env_.frame_env mission_frame) in
  let mission_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) mission_space) in
  time_expr mission_lit := 
  let frame_lit := (eval_.frame_eval env_.frame_env std_fr) in
  let std_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) std_sp) in
  let frame_lit := (eval_.frame_eval env_.frame_env mission_frame) in
  let mission_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) mission_space) in    
  let std_to_mission_lit :=   (eval_.transform_eval std_lit mission_lit) (env_.transform_env std_lit mission_lit) std_to_mission in
  let launch_time_lit :=      (eval_.time_eval std_lit) (env_.time_env std_lit) launch_time in
    time_expr.lit (std_to_mission_lit.transform_time launch_time_lit)


def mission_to_std : 
  let frame_lit := (eval_.frame_eval env_.frame_env std_fr) in
  let std_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) std_sp) in
  let frame_lit := (eval_.frame_eval env_.frame_env mission_frame) in
  let mission_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) mission_space) in
  transform_expr mission_lit std_lit 
  := 
  let frame_lit := (eval_.frame_eval env_.frame_env std_fr) in
  let std_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) std_sp) in
  let frame_lit := (eval_.frame_eval env_.frame_env mission_frame) in
  let mission_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) mission_space) in
  transform_expr.lit (mission_lit.time_tr std_lit)

--cannot deeply embed this due to type limitations
def std_to_std_compose := 
  let frame_lit := (eval_.frame_eval env_.frame_env std_fr) in
  let std_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) std_sp) in
  let frame_lit := (eval_.frame_eval env_.frame_env mission_frame) in
  let mission_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) mission_space) in
  let std_to_mission_lit :=   (eval_.transform_eval std_lit mission_lit) (env_.transform_env std_lit mission_lit) std_to_mission in
  let mission_to_std_lit :=   (eval_.transform_eval mission_lit std_lit) (env_.transform_env mission_lit std_lit) mission_to_std in
  transform_expr.compose_lit std_to_mission_lit mission_to_std_lit