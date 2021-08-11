import .lang.lang
open lang.time
open lang.geom1d
open lang.geom3d
open lang.series.geom3d
open lang.bool_expr
namespace peirce_output
noncomputable theory

def wt_fr : time_frame_expr := |time_std_frame|
def wt : time_space_expr wt_fr := |time_std_space|

def ww_fr : geom3d_frame_expr := |geom3d_std_frame|
def ww : geom3d_space_expr ww_fr := |geom3d_std_space|

def hw_fr : time_frame_expr := 
 let origin := |mk_time wt.value 4| in
 let basis := |mk_duration wt.value 1| in
 mk_time_frame_expr origin basis
def hw : time_space_expr hw_fr := mk_time_space_expr hw_fr

def ss_fr : time_frame_expr := 
 let origin := |mk_time wt.value 5| in
 let basis := |mk_duration wt.value 2| in
 mk_time_frame_expr origin basis
def ss : time_space_expr ss_fr := mk_time_space_expr ss_fr


def main : punit := 
  let hardware_clock_time : time_expr hw := ((|mk_time hw.value 6|:time_expr hw)) in
  let msg : timestamped_pose3d_expr hw ww := ((|mk_time hw.value 6,mk_pose3d ww.value 
    (mk_orientation3d ww.value 3 2 1 1 2 3 1 2 3)
    (mk_position3d ww.value 1 2 3)|:timestamped_pose3d_expr hw ww)) in
  let msg0 : timestamped_pose3d_expr hw ww := |{
    timestamp:=(((hardware_clock_time : time_expr hw))).value,
    ..msg.value
  }| in
  let _ros_time_base : time_expr wt := ((|mk_time wt.value 0|:time_expr wt)) in
  let stamp_added_bias : time_expr hw := ((((_ros_time_base : time_expr wt))+ᵥ((|msg0.value.timestamp| : _)):time_expr hw)) in
  let msg1 : timestamped_pose3d_expr hw ww := |{
    timestamp:=(((|mk_time hw.value 5|:time_expr hw))).value,
    ..msg0.value
  }| in

  punit.star



end peirce_output