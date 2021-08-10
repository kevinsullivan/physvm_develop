import .lang.expressions.time_expr
import .lang.expressions.geom1d_expr
import .lang.expressions.geom3d_expr
import tactic.linarith

--import ............
open lang.time
open lang.geom1d
open lang.geom3d
/-
FILE ONLY WORKS IN /peirce/ FOLDER

-/

namespace poutput

def World_fr : geom3d_frame_expr := |geom3d_std_frame|
def World : geom3d_space_expr World_fr := |geom3d_std_space|

def Target_fr : geom3d_frame_expr := 
 let origin := |mk_position3d World.value 1.000000 2.000000 3.000000| in
 let basis0 := |mk_displacement3d World.value 1.000000 2.000000 3.000000| in
 let basis1 := |mk_displacement3d World.value 1.000000 2.000000 3.000000| in
 let basis2 := |mk_displacement3d World.value 1.000000 2.000000 3.000000| in
 mk_geom3d_frame_expr origin basis0 basis1 basis2
def Target : geom3d_space_expr Target_fr := mk_geom3d_space_expr Target_fr

def IMU_fr : geom3d_frame_expr := 
 let origin := |mk_position3d World.value 3.000000 3.000000 3.000000| in
 let basis0 := |mk_displacement3d World.value 3.000000 3.000000 3.000000| in
 let basis1 := |mk_displacement3d World.value 3.000000 3.000000 3.000000| in
 let basis2 := |mk_displacement3d World.value 3.000000 3.000000 3.000000| in
 mk_geom3d_frame_expr origin basis0 basis1 basis2
def IMU : geom3d_space_expr IMU_fr := mk_geom3d_space_expr IMU_fr

noncomputable def msg : pose3d_expr IMU := |pose3d.mk (mk_orientation3d IMU.value 
  (mk_displacement3d IMU.value 1 2 3) (mk_displacement3d IMU.value 1 2 3) (mk_displacement3d IMU.value 1 2 3)) 
  (mk_position3d IMU.value 0 0 0)|

noncomputable def poseTmp : pose3d_expr Target := |pose3d.mk (mk_orientation3d Target.value 
  (mk_displacement3d Target.value 1 2 3) (mk_displacement3d Target.value 1 2 3) (mk_displacement3d Target.value 1 2 3)) 
  (mk_position3d Target.value 0 0 0)|

noncomputable def poseTmp_0 : pose3d_expr Target  := |{
  position := (mk_position3d IMU.value msg.value.position.x msg.value.position.y msg.value.position.z),
  ..poseTmp.value
}|

noncomputable def orientation : _ := |mk_orientation3d IMU.value (mk_displacement3d IMU.value 0 0 0) (mk_displacement3d IMU.value 0 0 0) (mk_displacement3d IMU.value 0 0 0)|

noncomputable def orientation_0 := |msg.value.orientation|

noncomputable def poseTmp_1 : pose3d_expr Target := | {
  orientation := orientation_0,
  ..poseTmp.value
}|

end poutput