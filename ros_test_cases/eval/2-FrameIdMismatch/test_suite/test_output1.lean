import ...lang.expressions.time_expr
--import .lang.expressions.geom1d_expr

--import .lang.expressions.geom3d_expr

--import ............
open lang.time
open lang.geom1d
open lang.geom3d
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



