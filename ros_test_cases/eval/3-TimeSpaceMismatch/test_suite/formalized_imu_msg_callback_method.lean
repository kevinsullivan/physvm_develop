import .phys.time.time
import .phys.time_series.geom3d
noncomputable theory

def world : geom3d_space geom3d_std_frame := geom3d_std_space
def wt : time_space time_std_frame := time_std_space
def hardware : time_space _ := 
  let origin := mk_time wt 1 in
  let basis := mk_duration wt 0.001 in 
  mk_space (mk_time_frame origin basis)
def system : time_space _ := 
  let origin := mk_time wt 20 in
  let basis := mk_duration wt 1 in 
  mk_space (mk_time_frame origin basis)
def system_seconds : time_space _ := 
  let origin := mk_time system 0 in
  let basis := mk_duration system 1 in 
  mk_space (mk_time_frame origin basis)
def hardware_seconds : time_space _ := 
  let origin := mk_time hardware 0 in
  let basis := mk_duration hardware 1000 in
  mk_space (mk_time_frame origin basis)

/-
This frame object is either timestamped Acceleration or Angular Velocity Vector. 
We have no implementation for either in Peirce (or for sum types for that matter).
Per discussion on last Friday, this is replaced with a Position3D
void BaseRealSenseNode::imu_callback_sync(rs2::frame frame, imu_sync_method sync_method)
-/
def imu_callback_sync : timestamped hardware (position3d world) → punit := 
  λ frame,
  --double frame_time = frame.get_timestamp();
  let frame_time := frame.timestamp in 
  /-setBaseTime(frame_time, frame.get_frame_timestamp_domain());
    _ros_time_base = ros::Time::now();
    _camera_time_base = frame_time;
  -/
  let _ros_time_base := mk_time system 0 in
  let _camera_time_base := frame_time in
--double elapsed_camera_ms = (/*ms*/ frame_time - /*ms*/ _camera_time_base) / 1000.0;
  let elapsed_camera_ms : duration hardware
    := (hardware.mk_time_transform_to hardware_seconds).transform_duration (frame_time -ᵥ _camera_time_base) in
    /-
        auto crnt_reading = *(reinterpret_cast<const float3*>(frame.get_data()));
        Eigen::Vector3d v(crnt_reading.x, crnt_reading.y, crnt_reading.z);
    -/
  let crnt_reading := frame.value in
  let v := mk_position3d world crnt_reading.x crnt_reading.y crnt_reading.z in
  --CimuData imu_data(stream_index, v, elapsed_camera_ms);
  let imu_data : timestamped hardware (position3d world) := ⟨elapsed_camera_ms, v⟩ in
  --std::deque<sensor_msgs::Imu> imu_msgs;
  --FillImuData_Copy(imu_data, imu_msgs);
  -- We can't really annotate these methods. We have no concept of an IMU message

  let imu_msgs : list (timestamped hardware (position3d world)) := [imu_data] in

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

  let t : time hardware_seconds :=
    mk_time _ 
    ((
      let _ros_time_base_toSec : time system → scalar := 
      λt, 
        let system_to_system_seconds := system.mk_time_transform_to system_seconds in
        (system_to_system_seconds.transform_time t).coord in
      _ros_time_base_toSec _ros_time_base
    )
    +
    (
      --casting time to duration discussed
      let imu_time_as_duration := mk_duration hardware imu_msg.timestamp.coord in 
      let _imu_msg_timestamp_toSec : duration hardware → scalar := 
        λt, 
          let hardware_to_hardware_seconds := hardware.mk_time_transform_to hardware_seconds in
          (hardware_to_hardware_seconds.transform_duration t).coord in
      _imu_msg_timestamp_toSec imu_time_as_duration
    )) in 
  
  
  punit.star