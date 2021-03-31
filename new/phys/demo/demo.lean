import data.real.basic 
import ..phys

/-
On standard_space impose a temporal coordinate system with t=0 at launch time and the unit of time is one second.
-/
def launch_time   /-: time (time_std_space ℚ)-/       := mk_time (time_std_space ℚ) 0
def one_second    /-: duration (time_std_space ℚ)-/   := mk_duration (time_std_space ℚ) 1
def time_frame                                        := mk_frame launch_time.to_point one_second.to_vectr -- TODO: Fix this API glitch
def mission_time                                      := mk_space ℚ time_frame -- TODO: should infer Q at this point in API

/-
Do some coordinate-free computations in this affine coordinate space
-/
def ego_launch_time                                   := mk_time mission_time 0
def t_plus_one_minute                                 := mk_time mission_time 60
def one_minute                                        := mk_duration mission_time 60
def t_plus_one_minute'                                := one_minute +ᵥ ego_launch_time     -- coordinate free in coordinate space
def t_plus_one_second                                 := one_second +ᵥ ego_launch_time     -- frame error

/-
Now make sure geom stuff is working equally well
-/



/-
Then model a dynamic system, e.g., in which a 
position varies with time, e.g., pos(t) = t.
-/