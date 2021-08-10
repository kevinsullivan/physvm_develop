import .lang.lang
open lang.time
open lang.geom1d
open lang.geom3d
open lang.series.geom3d
open lang.bool_expr
namespace peirce_output
noncomputable theory

def World_fr : geom3d_frame_expr := |geom3d_std_frame|
def World : geom3d_space_expr World_fr := |geom3d_std_space|

def IMU_fr : geom3d_frame_expr := 
 let origin := |mk_position3d World.value 1 2 3| in
 let basis0 := |mk_displacement3d World.value 1 2 3| in
 let basis1 := |mk_displacement3d World.value 1 2 3| in
 let basis2 := |mk_displacement3d World.value 1 2 3| in
 mk_geom3d_frame_expr origin basis0 basis1 basis2
def IMU : geom3d_space_expr IMU_fr := mk_geom3d_space_expr IMU_fr

def Target_fr : geom3d_frame_expr := 
 let origin := |mk_position3d World.value 3 2 1| in
 let basis0 := |mk_displacement3d World.value 3 2 1| in
 let basis1 := |mk_displacement3d World.value 3 2 1| in
 let basis2 := |mk_displacement3d World.value 3 2 1| in
 mk_geom3d_frame_expr origin basis0 basis1 basis2
def Target : geom3d_space_expr Target_fr := mk_geom3d_space_expr Target_fr


def main : punit := 
  let msg : pose3d_expr IMU := ((|mk_pose3d IMU.value 
    (mk_orientation3d IMU.value 1 2 3 1 2 3 1 2 3)
    (mk_position3d IMU.value 1 2 3)|:pose3d_expr IMU)) in
  let poseTmp : pose3d_expr Target := ((|mk_pose3d Target.value 
    (mk_orientation3d Target.value 1 2 3 1 2 3 1 2 3)
    (mk_position3d Target.value 4 3 2)|:pose3d_expr Target)) in
  let poseTmp0 : pose3d_expr Target := |{
    position:=(((|mk_position3d IMU.value 1 2 3|:position3d_expr IMU))).value,
    ..poseTmp.value
}| in
  let orientation : orientation3d_expr IMU := ((|mk_orientation3d_from_quaternion IMU.value 1 2 3 4|:orientation3d_expr IMU)) in
  let poseTmp1 : pose3d_expr Target := |{
    orientation:=(((orientation:orientation3d_expr IMU))).value,
    ..poseTmp0.value
}| in

  punit.star



end peirce_output