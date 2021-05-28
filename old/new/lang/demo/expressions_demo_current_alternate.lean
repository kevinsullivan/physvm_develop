import ..expressions.time_expr_current


open lang.time

--K is now an abbreviation - set to ℚ
def std_fr : time_frame_expr := [time_std_frame K] 
--def std_sp : time_space_expr std_fr :=  [mk_space K std_fr.value] --issue with has_lit type class
def std_sp : time_space_expr std_fr :=  [time_std_space K]

lemma p1 : std_sp.value = time_std_space K := rfl


/-
Use of new notation
-/
def launch_time : 
  time_expr std_sp
  :=
  [(mk_time (time_std_space K) 0)]

def one_second := 
  [(mk_duration std_sp.value 1)]

-- TODO: Introduce concrete syntax notations

/-
Frame definition updated with embedding into expression
-/
def mission_frame : time_frame_expr  := 
    mk_time_frame_expr launch_time one_second
/-
Construct a new space with this frame

def mission_time := mk_space ℚ (time_frame)
-/

/-
Space definition updated with embedding into expression
-/

def mission_space :=
  [(mk_space ℚ mission_frame.value)]


/-
Define new times and durations in terms of this new frame,
demonstrate 
-/

def ego_launch_time : 
  time_expr mission_space
  :=
  [(mk_time mission_space.value 0)]

def one_minute : 
  duration_expr mission_space
  := 
  [(mk_duration mission_space.value 60)]

def t_plus_one_minute' : _ := 
  one_minute +ᵥ ego_launch_time     -- coordinate free in coordinate space
def t_plus_one_second : _  := one_second +ᵥ ego_launch_time     -- frame error



--build a transform
def std_to_mission : 
  transform_expr std_sp mission_space  --type
  :=    
  [(std_sp.value.time_tr mission_space.value)] --value

#check std_to_mission.value

--transform original launch_time point in std_space to mission space
def launch_time_in_time_frame : 
  time_expr mission_space 
  := 
    [(std_to_mission.value.transform_time launch_time.value)]


def mission_to_std : 
  transform_expr mission_space std_sp
  := 
  [(mission_space.value.time_tr std_sp.value)]

--cannot deeply embed this due to type limitations
def std_to_std_compose := 
  transform_expr.compose_lit std_to_mission.value mission_to_std.value