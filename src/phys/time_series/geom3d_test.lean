import .geom3d
import tactic.linarith

def world_fr := geom3d_std_frame
def world := geom3d_std_space

def target_fr := 
 let origin := mk_position3d world 1.000000 2.000000 3.000000 in
 let basis0 := mk_displacement3d world 4.000000 3.000000 2.000000 in
 let basis1 := mk_displacement3d world 1.000000 2.000000 3.000000 in
 let basis2 := mk_displacement3d world 2.000000 1.000000 2.000000 in
 mk_geom3d_frame origin basis0 basis1 basis2

def target_sp := mk_geom3d_space target_fr

/-
Define a pose expressed over time, 
in the coordinate space induced by coordinate frame target_fr
Note that target_sp, and hence, target_fr, is fixed in this definition
-/

noncomputable def target_pose : pose3d_series time_std_space target_sp
  := mk_pose3d_series_empty _ _


noncomputable def target_pose1 :=
  target_pose.update (mk_time _ 1)
  (mk_pose3d _ (mk_orientation3d _ 1 2 1 1 1 1 1 1 1) (mk_position3d _ 1 1 1))

noncomputable def target_pose2 :=
  target_pose1.update (mk_time _ 2)
  (mk_pose3d _ (mk_orientation3d _ 2 2 2 2 2 2 2 2 2) (mk_position3d _ 2 2 2))

noncomputable def target_pose3 :=
  target_pose2.update (mk_time _ 3)
  (mk_pose3d _ (mk_orientation3d _ 3 3 3 3 3 3 3 3 3) (mk_position3d _ 3 3 3))

/-
suppose target_fr, the frame underlying the coordinate system of target_pose, 
varies over time

We define a frame 
-/

def target_fr_series : geom3d_frame_series time_std_space :=
  time_series.mk_empty

def target_fr_series1 :=
  target_fr_series.update (mk_time _ 1) target_fr

def target_fr_series2 :=
  target_fr_series.update (mk_time _ 2) (
    let origin := mk_position3d world 1.000000 3.000000 5.000000 in
    let basis0 := mk_displacement3d world 1.000000 3.000000 5.000000 in
    let basis1 := mk_displacement3d world 1.000000 3.000000 5.000000 in
    let basis2 := mk_displacement3d world 1.000000 3.000000 5.000000 in
    mk_geom3d_frame origin basis0 basis1 basis2)

def target_fr_series3 :=
  target_fr_series.update (mk_time _ 3) (
    let origin := mk_position3d world 4.000000 4.000000 4.000000 in
    let basis0 := mk_displacement3d world 4.000000 4.000000 4.000000 in
    let basis1 := mk_displacement3d world 4.000000 4.000000 4.000000 in
    let basis2 := mk_displacement3d world 4.000000 4.000000 4.000000 in
    mk_geom3d_frame origin basis0 basis1 basis2)

/-

However, assuming the intended meaning of this is that 
the frame of the pose (or coordinate system induced by the frame) varies over time,
expressed by target_fr_series,
there is nothing concrete linking the target_pose variable to the target_fr_series
variable. target_pose has a fixed coordinate system, or frame, and the target_fr 
series_variable has no concrete link to the target_pose variable. 

Thus, the coordinate system of target_pose is, according to our system, fixed,
which does not reflect the reality of the system we are modeling.

-/



example : target_pose3.sample (mk_time _ 1) = (inhabited.default _) := sorry

example : target_pose3.sample (mk_time _ (3)) = 
  (mk_pose3d _ (mk_orientation3d _ 3 3 3 3 3 3 3 3 3) (mk_position3d _ 3 3 3))
  := sorry

noncomputable def target_pose_discrete : pose3d_discrete time_std_space target_sp
  := mk_pose3d_discrete_empty time_std_space target_sp


noncomputable def target_pose_discrete1 :=
  target_pose_discrete.update (mk_time _ 1)
  (mk_pose3d _ (mk_orientation3d _ 1 1 1 1 1 1 1 1 1) (mk_position3d _ 1 1 1))

noncomputable def target_pose_discrete2 :=
  target_pose_discrete1.update (mk_time _ 2)
  (mk_pose3d _ (mk_orientation3d _ 2 2 2 2 2 2 2 2 2) (mk_position3d _ 2 2 2))

noncomputable def target_pose_discrete3 :=
  target_pose_discrete2.update (mk_time _ 3)
  (mk_pose3d _ (mk_orientation3d _ 3 3 3 3 3 3 3 3 3) (mk_position3d _ 3 3 3))

#check target_pose_discrete3.sample (mk_time _ (-1))


example : target_pose_discrete3.sample_floor (mk_time _ 1.5) = 
  (mk_pose3d _ (mk_orientation3d _ 1 1 1 1 1 1 1 1 1) (mk_position3d _ 1 1 1)) 
  := sorry
example : target_pose_discrete3.sample_floor (mk_time _ 3.5) = 
  (mk_pose3d _ (mk_orientation3d _ 3 3 3 3 3 3 3 3 3) (mk_position3d _ 3 3 3))
  := sorry
example : target_pose_discrete3.sample_floor (mk_time _ 0.5) = 
  (inhabited.default _) := sorry

example : target_pose_discrete3.sample (mk_time _ 1) = 
  (mk_pose3d _ (mk_orientation3d _ 1 1 1 1 1 1 1 1 1) (mk_position3d _ 1 1 1))
  := sorry --rfl

def target_pos : position3d_discrete time_std_space geom3d_std_space := 
  mk_position3d_discrete_empty _ _

def target_pos1 :=
  --target_pos.update (mk_time _ 1) (mk_position3d _ 1 1 1)
  (target_pos : list (time time_std_space × position3d geom3d_std_space)) ++ 
  [((mk_time _ 1),(mk_position3d _ 1 1 1))]

def target_pos2 :=
  target_pos1.update (mk_time _ 2) (mk_position3d _ 2 2 2)

def target_pos3 :=
  target_pos2.update (mk_time _ 3) (mk_position3d _ 3 3 3)

example : (target_pos3.sample_floor (mk_time _ 1.5)).x = 1
  := sorry



#eval (target_pos3.sample_floor (mk_time _ 35)).z

#eval (target_pos3.sample (mk_time _ 1)).z

#eval target_pos3.length

--#eval 

example : target_pose3.sample (mk_time _ 1) = 
  (mk_pose3d _ (mk_orientation3d _ 1 1 1 1 1 1 1 1 1) (mk_position3d _ 1 1 1))
  := sorry
