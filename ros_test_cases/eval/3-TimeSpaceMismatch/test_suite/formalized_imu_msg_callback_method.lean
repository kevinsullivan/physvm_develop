import .phys.time.time
import .phys.time_series.geom3d
import .standards.time_std
noncomputable theory
/-
https://www.intelrealsense.com/how-to-getting-imu-data-from-d435i-and-t265/#Tracking_Sensor_Origin_and_CS
1. The positive x-axis points to the right.
2. The positive y-axis points down.
3. The positive z-axis points forward
-/
def camera_imu_fr : geom3d_frame := 
 let origin := mk_position3d geom3d_std_space 0 0 0 in
 let basis0 := mk_displacement3d geom3d_std_space 1.000000 0 0 in
 let basis1 := mk_displacement3d geom3d_std_space 0 0 (-1) in
 let basis2 := mk_displacement3d geom3d_std_space 0 1 0 in
 mk_geom3d_frame origin basis0 basis1 basis2
def camera_imu : geom3d_space camera_imu_fr := mk_geom3d_space camera_imu_fr
/-
To avoid uninitended equality in Lean of "spaces" (because we conventionally use std_frame)
should we always create an application-specific camera_imu_space of a type that's different than
std_space?
-/

/-
Note : 8/13
We do not have access to the source code showing how this is populated. 
All we know is that this measurement comes from the realsense camera -
where the "system_time_in_seconds" clock comes from the local machine.
-/

def hardware_time_ms : time_space _ := 
  let hardware_clock_time_offset : scalar := 0.470 in
  let milliseconds := 1000 in
  let origin := mk_time coordinated_universal_time_in_seconds hardware_clock_time_offset in
  let basis := mk_duration coordinated_universal_time_in_seconds milliseconds in 
  mk_space (mk_time_frame origin basis)
/-
Hardware time in what units?
-/

def system_time_in_seconds := 
  let local_system_clock_time_offset : scalar := 0.870 in
  let seconds := 0.001 in
  let origin := mk_time coordinated_universal_time_in_seconds local_system_clock_time_offset in
  let basis := mk_duration coordinated_universal_time_in_seconds seconds in 
  mk_space (mk_time_frame origin basis)

/-
Isn't this the same as the one above? 

What coordinates to use in these definitions
is not well defined at the moment. We need a
foundational time standard in terms of which 
all our other coordinate systems are defined.

Unix time rests of expression of origin time
in UTC. UTC is based on International Atomic
Time (TAI). That could be our foundational
coordinate system. Or is there something even
more fundamental. 
-/


/-
Question: hardware_time_seconds_but_what's_the_origin
The origin is 0 with respect to the hardware frame
-/
def hardware_time_seconds : time_space _ := 
  let milliseconds_to_seconds := 0.001 in
  let origin := mk_time hardware_time_ms 0 in
  let basis := mk_duration hardware_time_ms milliseconds_to_seconds in
  mk_space (mk_time_frame origin basis)

/-
This frame object is either timestamped Acceleration or Angular Velocity Vector. 
We have no implementation for either in Peirce (or for sum types for that matter).
Per discussion on last Friday, this is replaced with a Position3D
void BaseRealSenseNode::imu_callback_sync(rs2::frame frame, imu_sync_method sync_method)
-/
def imu_callback_sync : timestamped hardware_time_ms (position3d camera_imu) → punit := 
  λ frame,
  --double frame_time = frame.get_timestamp();
  let frame_time := frame.timestamp in 
  /-setBaseTime(frame_time, frame.get_frame_timestamp_domain());
    _ros_time_base = ros::Time::now();
    _camera_time_base = frame_time;
  -/
  let _ros_time_base := mk_time system_time_in_seconds 0 in
  let _camera_time_base := frame_time in
--double elapsed_camera_ms = (/*ms*/ frame_time - /*ms*/ _camera_time_base) / 1000.0;
  let elapsed_camera_ms : duration hardware_time_ms
    := (hardware_time_ms.mk_time_transform_to hardware_time_seconds).transform_duration (frame_time -ᵥ _camera_time_base) in
    /-
        auto crnt_reading = *(reinterpret_cast<const float3*>(frame.get_data()));
        Eigen::Vector3d v(crnt_reading.x, crnt_reading.y, crnt_reading.z);
    -/
  let crnt_reading := frame.value in
  let v := mk_position3d camera_imu crnt_reading.x crnt_reading.y crnt_reading.z in
  --CimuData imu_data(stream_index, v, elapsed_camera_ms);
  let imu_data : timestamped hardware_time_ms (position3d camera_imu) := ⟨elapsed_camera_ms, v⟩ in
  --std::deque<sensor_msgs::Imu> imu_msgs;
  --FillImuData_Copy(imu_data, imu_msgs);
  -- We can't really annotate these methods. We have no concept of an IMU message

  let imu_msgs : list (timestamped hardware_time_ms (position3d camera_imu)) := [imu_data] in

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
      let _ros_time_base_toSec : time system_time_in_seconds → scalar := 
      λt, 
        (t).coord in
      _ros_time_base_toSec _ros_time_base
    )
    +
    (
      --casting time to duration discussed
      let imu_time_as_duration := mk_duration hardware_time_ms imu_msg.timestamp.coord in 
      let _imu_msg_timestamp_toSec : duration hardware_time_ms → scalar := 
        λt, 
          let hardware_to_hardware_seconds := hardware_time_ms.mk_time_transform_to hardware_time_seconds in
          (hardware_to_hardware_seconds.transform_duration t).coord in
      _imu_msg_timestamp_toSec imu_time_as_duration
    )) in 
  
  
  punit.star