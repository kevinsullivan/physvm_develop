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

def BaseLink_fr : geom3d_frame_expr := 
 let origin := |mk_position3d World.value 1 2 3| in
 let basis0 := |mk_displacement3d World.value 1 2 3| in
 let basis1 := |mk_displacement3d World.value 1 2 3| in
 let basis2 := |mk_displacement3d World.value 1 2 3| in
 mk_geom3d_frame_expr origin basis0 basis1 basis2
def BaseLink : geom3d_space_expr BaseLink_fr := mk_geom3d_space_expr BaseLink_fr

def UTM_fr : geom3d_frame_expr := 
 let origin := |mk_position3d World.value 3 2 1| in
 let basis0 := |mk_displacement3d World.value 3 2 1| in
 let basis1 := |mk_displacement3d World.value 4 4 4| in
 let basis2 := |mk_displacement3d World.value 4 5 5| in
 mk_geom3d_frame_expr origin basis0 basis1 basis2
def UTM : geom3d_space_expr UTM_fr := mk_geom3d_space_expr UTM_fr

def BaseLinkYawOnly_fr : geom3d_frame_expr := 
 let origin := |mk_position3d World.value 1 2 3| in
 let basis0 := |mk_displacement3d World.value 5 5 5| in
 let basis1 := |mk_displacement3d World.value 5 5 5| in
 let basis2 := |mk_displacement3d World.value 5 6 6| in
 mk_geom3d_frame_expr origin basis0 basis1 basis2
def BaseLinkYawOnly : geom3d_space_expr BaseLinkYawOnly_fr := mk_geom3d_space_expr BaseLinkYawOnly_fr


def main : punit := 
  let transform_world_pose_ : geom3d_transform_expr World BaseLink := ((|World.value.mk_geom3d_transform_to BaseLink.value|:geom3d_transform_expr World BaseLink)) in
  let cartesian_world_transform_ : geom3d_transform_expr World UTM := ((|World.value.mk_geom3d_transform_to UTM.value|:geom3d_transform_expr World UTM)) in
  let cartesian_pose_with_orientation : geom3d_transform_expr UTM BaseLinkYawOnly := ((|UTM.value.mk_geom3d_transform_to BaseLinkYawOnly.value|:geom3d_transform_expr UTM BaseLinkYawOnly)) in
  let cartesian_world_transform_0 : geom3d_transform_expr World UTM := ((transform_world_pose_ : geom3d_transform_expr World BaseLink)).value∘((((cartesian_pose_with_orientation : geom3d_transform_expr UTM BaseLinkYawOnly))⁻¹:geom3d_transform_expr BaseLinkYawOnly UTM)).value in

  punit.star



end peirce_output