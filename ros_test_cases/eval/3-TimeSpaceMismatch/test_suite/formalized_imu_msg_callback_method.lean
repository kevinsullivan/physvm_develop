import .phys.time.time
import .phys.time_series.geom3d
import .standards.time_std
noncomputable theory

/-
This sensor-streaming application runs in some assumed 
world with 3-d geometry and time as physical dimensions. 
We import and will build from phys.geom and phys.time,
each of which comes with an uninterpreted "standard"
coordinate system.
-/

/-
We need to assume a physical interpretation of the data
that represents our world affine coordinate system. So
here's what we'll assume.

(1) ORIGIN: the world_geom_acs.origin represents the 
northwest-ish (back right) lower corner of the Rice Hall
Less Lab

(2) BASIS VECTORS
    basis0 
      - points right/east along the wall
      - unit length is 1m 
      - right handed chirality
    basis1 
      - points to the door along the west wall, 
      - unit length is 1m
      - RHC
    basis2 
      - points up along the NW corner of the room, 
      - unit length is one meter, 
      - RHC

Some notes on Chirality/"Handedness":
https://en.wikipedia.org/wiki/Orientation_(vector_space)
http://www.cs.cornell.edu/courses/cs4620/2008fa/asgn/ray1/fcg3-sec245-248.pdf


(3) ACS is given by [Origin, b0, b1, b2]

-/
def geometry3d_acs : geom3d_space _ := 
 let origin := mk_position3d geom3d_std_space 0 0 0 in
 let basis0 := mk_displacement3d geom3d_std_space 1 0 0 in
 let basis1 := mk_displacement3d geom3d_std_space 0 1 0 in
 let basis2 := mk_displacement3d geom3d_std_space 0 0 1 in
 let fr := mk_geom3d_frame origin basis0 basis1 basis2 in
  mk_geom3d_space fr
  /-
  Note that world_geom_acs is not definitionally equal to
  geom3d_std_space because the latter uses fm.base as its
  frame, while world-geom_acs uses a frame defined by the
  fm.deriv constructor.
  -/

/-
We need to assume a physical interpretation of the data
representing our coordinate system on time.

(1) ORIGIN: January 1, 1970 per UTC standard

(2) BASIS VECTORS
    basis0 
      - points to the future
      - unit length is 1 second 

(3) ACS is given by [Origin, b0]
-/
def time_acs : time_space _ := coordinated_universal_time_in_seconds
--  let origin := mk_time time_std_space 0 in
--  let basis := mk_duration time_std_space 1 in
--  let fr := mk_time_frame origin basis in
--  mk_time_space fr


/-
We're assuming a RealSense D435I hardware
unit. It comes with a defined coordinate
system
We'll assume that the camera_imu is two
meters to the right along the back wall,
one meter out from the wall and one meter
high. We'll inhert the standard vector 
space structure from the world_geom_acs.

That's its position in space. As for its
orientation, we'll assume that 

1. The positive x-axis points to the subject.
2. The positive y-axis points down.
3. The positive z-axis points forward
-/
def camera_imu_acs : geom3d_space _ := 
 let origin := mk_position3d geometry3d_acs 2 1 1 in
 let basis0 := mk_displacement3d geometry3d_acs 1 0 0 in
 let basis1 := mk_displacement3d geometry3d_acs 0 0 (-1) in
 let basis2 := mk_displacement3d geometry3d_acs 0 1 0 in
 let fr := mk_geom3d_frame origin basis0 basis1 basis2 in
  mk_geom3d_space fr
-- https://www.intelrealsense.com/how-to-getting-imu-data-from-d435i-and-t265/#Tracking_Sensor_Origin_and_CS



/-
We will assume that the origin of the camera's affine coordinate system is the same as UTC,
so we're using the origin of UTC as the origin Camera's time frame.

(1) ORIGIN: 0 seconds AHEAD of our standard UTC origin

(2) BASIS VECTORS
    basis0 
      - points to the future
      - unit length is 1 millisecond

(3) ACS is given by [Origin, b0]
-/

/-RealSense developers refer to this as the hardware domain-/
def camera_time_acs : time_space _ := 
  let hardware_clock_time_offset : scalar := 0.0 in
  let milliseconds := 1000 in
  let origin := mk_time coordinated_universal_time_in_seconds hardware_clock_time_offset in
  let basis := mk_duration coordinated_universal_time_in_seconds milliseconds in 
  mk_time_space (mk_time_frame origin basis)

/-
Question: hardware_time_seconds_but_what's_the_origin
The origin is 0 with respect to the hardware frame
-/
def hardware_time_seconds : time_space _ := 
  let milliseconds_to_seconds := 0.001 in
  let origin := mk_time camera_time_acs 0 in
  let basis := mk_duration camera_time_acs milliseconds_to_seconds in
  mk_time_space (mk_time_frame origin basis)
/-
Hardware time in what units?
-/

/-
This is the consuming ROS node's system time expressed in units seconds

(1) ORIGIN: .87 seconds AHEAD of our standard UTC origin

(2) BASIS VECTORS
    basis0 
      - points to the future
      - unit length is 1 second

(3) ACS is given by [Origin, b0]
-/

def platform_time_in_seconds := 
  let local_system_clock_time_offset : scalar := 0.870 in
  let seconds := 0.001 in
  let origin := mk_time coordinated_universal_time_in_seconds local_system_clock_time_offset in
  let basis := mk_duration coordinated_universal_time_in_seconds seconds in 
  mk_time_space (mk_time_frame origin basis)

/-
This frame object is either timestamped Acceleration or Angular Velocity Vector. 
We have no implementation for either in Peirce (or for sum types for that matter).
Per discussion on last Friday, this is replaced with a Position3D
void BaseRealSenseNode::imu_callback_sync(rs2::frame frame, imu_sync_method sync_method)
-/
def imu_callback_sync : timestamped camera_time_acs (position3d camera_imu_acs) → punit := 
  λ frame,
  --double frame_time = frame.get_timestamp();
  let frame_time := frame.timestamp in 
  /-setBaseTime(frame_time, frame.get_frame_timestamp_domain());
    _ros_time_base = ros::Time::now();
    _camera_time_base = frame_time;
  -/
  let _ros_time_base := mk_time platform_time_in_seconds 0 in
  let _camera_time_base := frame_time in
--double elapsed_camera_ms = (/*ms*/ frame_time - /*ms*/ _camera_time_base) / 1000.0;
  let elapsed_camera_ms : duration camera_time_acs
    := (camera_time_acs.mk_time_transform_to hardware_time_seconds).transform_duration (frame_time -ᵥ _camera_time_base) in
    /-
        auto crnt_reading = *(reinterpret_cast<const float3*>(frame.get_data()));
        Eigen::Vector3d v(crnt_reading.x, crnt_reading.y, crnt_reading.z);
    -/
  let crnt_reading := frame.value in
  let v := mk_position3d camera_imu_acs crnt_reading.x crnt_reading.y crnt_reading.z in
  --CimuData imu_data(stream_index, v, elapsed_camera_ms);
  let imu_data : timestamped camera_time_acs (position3d camera_imu_acs) := ⟨elapsed_camera_ms, v⟩ in
  --std::deque<sensor_msgs::Imu> imu_msgs;
  --FillImuData_Copy(imu_data, imu_msgs);
  -- We can't really annotate these methods. We have no concept of an IMU message

  let imu_msgs : list (timestamped camera_time_acs (position3d camera_imu_acs)) := [imu_data] in

  --std::deque<sensor_msgs::Imu> imu_msgs;
  --FillImuData_Copy(imu_data, imu_msgs);
  --
  --sensor_msgs::Imu imu_msg = imu_msgs.front();
  let imu_msg := imu_msgs.head in
  --ros::Time t(_ros_time_base.toSec() + imu_msg.header.stamp.toSec());
  /-
  Discussion from Tuesday - ho℘ to annotate this
  
  Involves complex, context-dependent interpretation of toSec() 
  The result of this calculation should contain an error, 
    but there is no problem with adding together two scalars
  An alternative 
  -/

  let t : time hardware_time_seconds :=
    mk_time _ 
    ((
      let _ros_time_base_toSec : time platform_time_in_seconds → scalar := 
      λt, 
        (t).coord in
      _ros_time_base_toSec _ros_time_base
    )
    +
    (
      --casting time to duration discussed
      let imu_time_as_duration := mk_duration camera_time_acs imu_msg.timestamp.coord in 
      let _imu_msg_timestamp_toSec : duration camera_time_acs → scalar := 
        λt, 
          let hardware_to_hardware_seconds := camera_time_acs.mk_time_transform_to hardware_time_seconds in
          (hardware_to_hardware_seconds.transform_duration t).coord in
      _imu_msg_timestamp_toSec imu_time_as_duration
    )) in 
  
  
  punit.star