import ..expressions.time_expr_current

open lang.time
/-
Stress test of alternate API

First Frames, then Spaces, 
Duration, Time, Transforms

Type error demonstrations on bottom
-/

--check frame API
def std_fr : time_frame_expr := [time_std_frame K] 
def fr_var : time_frame_var := ⟨⟨"std"⟩⟩ --hide with function?
def fr_var_expr := time_frame_expr.var fr_var
#check fr_var_expr.value
lemma defaultedfr : fr_var_expr.value = time_std_frame K := rfl

--check space API
def std_sp : time_space_expr std_fr :=  [time_std_space K]
def std_var : time_space_expr std_fr := time_space_expr.var ⟨⟨"std"⟩⟩
lemma defaultsp : std_var.value = std_sp.value := rfl

--out of sequence but required to test derived API
def launch_time : 
  time_expr std_sp
  :=
  [(mk_time std_sp.value 0)]
def one_second := 
  [(mk_duration std_sp.value 1)]

--test derived API
--This is not deeply embedded. Evaluates launch time and one second to build a new frame. 
--This is a trade-off caused because time frame expressions are defined prior to point and vector expressions,
--in order to allow points and vectors to depend on space expressions rather than phys space literal values,
--encapsulating phys inside of lang 
def mission_frame : time_frame_expr  := 
    mk_time_frame_expr launch_time one_second

--use this or literal constructor (this function uses a different constructor than [])
def mission_space :=
  mk_time_space_expr mission_frame --(mk_space ℚ mission_frame.value)

--move on to durations and times
def dur_zero : duration_expr std_sp := 0 --duration.zero
def dur_one : duration_expr std_sp := 1 --duration.one
def dur_lit : duration_expr std_sp := [one_second.value]
def dur_var : duration_expr std_sp := duration_expr.var ⟨⟨"dur"⟩⟩ -- var constructor should have notation?
def dur_add  : duration_expr std_sp := one_second +ᵥ one_second
def dur_neg  : duration_expr std_sp := -one_second
def dur_sub  : duration_expr std_sp := one_second -ᵥ 0 -ᵥ one_second 
def dur_time  : duration_expr std_sp := launch_time -ᵥ launch_time
def dur_smul  : duration_expr std_sp := (3:ℚ/-again, ℚ is K, the configured scalar field-/)•one_second

def time_lit : time_expr std_sp := [launch_time.value]
def time_var : time_expr std_sp := time_expr.var ⟨⟨"time"⟩⟩
def time_add : time_expr std_sp := one_second +ᵥ launch_time -- need to add reverse notation


--Test Transforms next
def transform_lit : 
  transform_expr std_sp mission_space :=  [(std_sp.value.time_tr mission_space.value)]
def transform_var : transform_expr std_sp mission_space := transform_expr.var ⟨⟨"tr"⟩⟩

--belongs with time and duration tests, but...
--also, these cannot be deeply embedded
--required to evaluate the point or vector operand
--needs notation?
def dur_apply : duration_expr mission_space := 
  duration_expr.apply_duration_lit transform_lit one_second.value
def time_apply : time_expr mission_space :=
  time_expr.apply_time_lit transform_lit launch_time.value

--used for compose
def mission_to_std : 
  transform_expr mission_space std_sp
  := 
  [(mission_space.value.time_tr std_sp.value)]
def std_to_mission := transform_lit
--compose result (trans used by mathlib)
--compose not deeply embedded, same limitation as apply
def std_to_std : transform_expr std_sp std_sp := std_to_mission.trans mission_to_std

--inverse
--inverse not deeply embedded, same limitation as apply
def mission_to_std' : 
  transform_expr mission_space std_sp := std_to_mission⁻¹


--a few type errors

--adding wrong spaces/frames
def mission_dur : duration_expr mission_space := [(mk_duration mission_space.value 1)]
def wrong_spaces := mission_dur +ᵥ dur_lit --dur_lit in standard space

--bad apply
def bad_apply := duration_expr.apply_duration_lit mission_to_std dur_lit --dur_lit not in mission space

--bad compose
def bad_compose := std_to_mission.trans std_to_mission 

--adding points
def point_add := launch_time +ᵥ launch_time 