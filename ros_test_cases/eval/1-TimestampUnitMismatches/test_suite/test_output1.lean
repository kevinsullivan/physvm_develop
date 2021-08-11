import .lang.lang
open lang.time
open lang.geom1d
open lang.geom3d
open lang.series.geom3d
open lang.bool_expr
namespace peirce_output
noncomputable theory

#check lift_t

def seconds_fr : time_frame_expr := |time_std_frame|
def seconds : time_space_expr seconds_fr := |time_std_space|

def nanoseconds_fr : time_frame_expr := 
 let origin := |mk_time seconds.value 0| in
 let basis := |mk_duration seconds.value 0.000000001| in
 mk_time_frame_expr origin basis
def nanoseconds : time_space_expr nanoseconds_fr := mk_time_space_expr nanoseconds_fr


def main : punit := 
  let durations : list (duration_expr seconds) := (([]:_)) in
  let durations0 : list (duration_expr seconds) := durations ++ [(((|mk_duration seconds.value 0| : duration_expr nanoseconds):duration_expr seconds))] in

  punit.star



end peirce_output