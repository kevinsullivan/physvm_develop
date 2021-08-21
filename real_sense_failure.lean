import .phys.time.time
import .phys.time_series.geom3d
import .standards.time_std
noncomputable theory

/-
This sensor-streaming application runs in an assumed 
world with 3-d geometry and time as physical dimensions. 
We import and will build from phys.geom and phys.time.
These modules provide a 3d geometric affine space and
1d temporal affine space, each with an uninterpreted 
"standard" coordinate system. The user of the library
must specify external-world interpretations for origin
and basis vectors.
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
  Another way to say the same thing perhaps?
  But now it's clearer that this is where we
  have to attach those extra semantics the raw
  geometric objects used here. In particular,
  the origin and each vector needs a physical
  interpretation, including both orientation
  and handedness.
  -/
  def geometry3d_acs' : geom3d_space _ := 
  (mk_geom3d_space 
    (mk_geom3d_frame 
      (mk_position3d geom3d_std_space 0 0 0)
      (mk_displacement3d geom3d_std_space 1 0 0)
      (mk_displacement3d geom3d_std_space 0 1 0)
      (mk_displacement3d geom3d_std_space 0 0 1)
    )
  )

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

--Andrew 8/17: I have changed the origin back to a non-zero value based on our discussion and confirmation today
that there is likely a small delta between the origins of differing devices. 
Candidly, my  desktop has an offset of -.612 seconds from UTC, my laptop -.413, and my phone +.026.  

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
def camera_time_seconds : time_space _ := 
  let milliseconds_to_seconds := 0.001 in
  let origin := mk_time camera_time_acs 0 in
  let basis := mk_duration camera_time_acs milliseconds_to_seconds in
  mk_time_space (mk_time_frame origin basis)
/-
Hardware time in what units?
-/

/-
This is the consuming ROS node's system time expressed in units seconds

One gap here is that this will be used to annotate the system time, which has a native
representation of seconds + nanoseconds, so there is arguably some mismatch when we
annotate the ros::Time variable simply as having units in seconds.

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
The parameter of the method imu_callback_sync, "frame", is either timestamped Acceleration or Angular Velocity Vector. 
We have no implementation for either in Peirce (or for sum types for that matter).
Per discussion on last 8/6, this is replaced with a Displacement3D.

void BaseRealSenseNode::imu_callback_sync(rs2::frame dataframe, imu_sync_method sync_method)
-/
def imu_callback_sync : timestamped camera_time_acs (displacement3d camera_imu_acs) → punit := 
  /-
  We define the argument to the method, dataframe. It has an interpretation of 
    timestamped camera_time_acs (position3d camera_imu_acs)
  , although it's actual physical type manifest in the code would be an Acceleration or Angular Velocity Vector, representing
  a timestamped reading coming from a Gyroscope or Accelerometer.
  -/
  λ dataframe, 
  /- 
    double frame_time = frame.get_timestamp();

    In this line, we extract the timestamp of the dataframe, which represents the timestamp at which the IMU data was gathered.
  -/
  let dataframe_time := dataframe.timestamp in 
  /-setBaseTime(frame_time, frame.get_frame_timestamp_domain());
    _ros_time_base = ros::Time::now();
    _camera_time_base = frame_time;

    A call is made to the method "setBaseTime". setBaseTime contains two salient lines: setting both _ros_time_base and
    _camera_time_base. _ros_time_base is intended to represent the first time point at which the camera
    has sent an IMU data reading, expressed in terms of of the local system clock that is reading
    data from the RealSense camera data feed. _camera_time_base is intended to represent the first time point at which the camera
    has sent an IMU data reading, expressed in terms of the clock directly on the camera.
  -/
  let _ros_time_base := mk_time platform_time_in_seconds 1629200210 in
  let _camera_time_base := dataframe_time in
--double elapsed_camera_ms = (/*ms*/ frame_time - /*ms*/ _camera_time_base) / 1000.0;
/-
  We take the difference between the first camera measurement, when the method "imu_callback_sync" was first called, and 
  the current camera measurement, as contained in "dataframe_time". Thus, the resulting difference is a duration in time.
  The variable name suggests that the resulting computation is in milliseconds. The dataframe_time and the _camera_time_base 
  are expressed in milliseconds due to the implementation of the camera's clock, however, the actual units are expressed in seconds,
  as there is a division by 1000. Thus, we transform the duration from its native millisecond frame to a seconds ACS. Mathematically, 
  we might represent this as Tₘˢ(t₂-t₁). Finally,
  there is a type error, as we are attempting to assign a value in an ACS representing seconds to a variable in an ACS
  representing milliseconds, which portrays a misconception by the developer when naming this variable.
-/
  let elapsed_camera_ms : duration camera_time_acs
    := (camera_time_acs.mk_time_transform_to camera_time_seconds).transform_duration (dataframe_time -ᵥ _camera_time_base) in
    /-
        auto crnt_reading = *(reinterpret_cast<const float3*>(frame.get_data()));
        Eigen::Vector3d v(crnt_reading.x, crnt_reading.y, crnt_reading.z);

        There are some uneventful assignments that occur here. 
        The first casts (via static_casting) the vector-quantity data that the frame argument encapsulates to a "float3 object" 
        and stores it into a variable named "crnt_reading". 
        The second converts the prior "float3" object into an "Eigen::Vector3d" object, by extracting its x, y, and z coordinates,
        using those respectively in the constructor to Eigen::Vector3d, and binding the constructed value into a variable called v. 

        We model in this in Lean simply by defining a value called "crnt_reading" and assigning the vector-valued data property stored in the 
        timestamped dataframe method argument. Since the physical type of the dataframe is "timestamped camera_time_acs (displacement3d camera_imu_acs)",
        we know that the type of crnt_reading must simply be "displacement3d camera_imu_acs".

        Next, we construct the vector v in the code. We define a variable v, which, again, has the physical type "displacement3d camera_imu_acs",
          since it is built by simply constructing a new displacement3d using the exact same x, y, and z coordinates of the prior value, crnt_reading.
    -/
  let crnt_reading : displacement3d camera_imu_acs := dataframe.value in
  let v : displacement3d camera_imu_acs := mk_displacement3d camera_imu_acs crnt_reading.x crnt_reading.y crnt_reading.z in
  --CimuData imu_data(stream_index, v, elapsed_camera_ms);
  /-
  The constructor of CimuData in the next line of code simply re-packages the vector data stored in the original frame argument,
  whose physical interpretation was a timestamped displacement3d in the camera, back into an another object which represents
  a timestamped displacement3d, but this time, the timestamp is expressed in terms of the camera_time_seconds ACS, as the developer
  explicitly converted from milliseconds into seconds when constructing what is intended to be the timestamp, elapsed_camera_seconds.
  
  Thus, in order to formalize this in Lean, declare a variable called "imu_data" with type "timestamped camera_time_seconds (displacement3d camera_imu_acs)", 
  and populate it using the vector-valued data v (which is, again, the same displacement3d encapsulated in the argument to the method), 
  as well as the variable "elapsed_camera_ms" as a timestamp, which, again is a duration, not a point, 
  as it is the result of subtracting two time variables, and so, we see an error here in our formalization.
  -/
  let imu_data : timestamped camera_time_seconds (displacement3d camera_imu_acs) := ⟨elapsed_camera_ms, v⟩ in
  /-
  std::deque<sensor_msgs::Imu> imu_msgs;
  switch (sync_method)
  {
      case NONE: //Cannot really be NONE. Just to avoid compilation warning.
      case COPY:
          FillImuData_Copy(imu_data, imu_msgs);
          break;
      case LINEAR_INTERPOLATION:
          FillImuData_LinearInterpolation(imu_data, imu_msgs);
          break;
  }
  -/
  /-
  We define a double-ended queue called "imu_msgs" and attempt to populate it. A call is made to the procedure "FillImuData_Copy"
  or "FillImuData_LinearInterpolation", which is omitted here. The purpose of these procedures includes are to construct IMU messages, 
  specifically tuples of 2 3-dimensional (non-geometric) vectors, along with a linear interpolation that are beyond 
  the scope of what we can currently formalize, and the resulting IMU messages stores either 0 (if the dataframe argument came from an accelerometer), 
  1 (if the dataframe argument came from a gyroscope and sync_method is set to "COPY"), or n (if the dataframe argument came from a gyroscope 
  and sync_method is set to "LINEAR_INTERPOLATION") into deque "imu_msgs". The purpose of the method call is that entries are added to imu_msgs, so this is
  simulated by simply instantiating the list with an initial value: imu_data - the timestamped value that we've constructed above. Note that
  due to our limitations in Peirce, we have annotated the type of imu_msgs as being the type of the data that we have available, 
    "(timestamped camera_time_seconds (displacement3d camera_imu_acs))", as opposed to a timestamped IMU message, since we are not yet able to formalize the latter.
  -/

  let imu_msgs : list (timestamped camera_time_seconds (displacement3d camera_imu_acs)) := [imu_data] in

  /-
  
  while (imu_msgs.size())
  {
      sensor_msgs::Imu imu_msg = imu_msgs.front();
  -/
  /-
  We now process each entry in the deque. Each entry has its timestamp updated, then it is published, and then it is removed from the queue, until the queue is empty.

  Firstly, we retrieve the front of the queue, which is simply a call to "list.head" in Lean, and, 
  since "imu_msgs" has type "list (timestamped camera_time_seconds (displacement3d camera_imu_acs))",
  the resulting expression is simply of type "(timestamped camera_time_seconds (displacement3d camera_imu_acs))"
  -/
  let imu_msg : timestamped camera_time_seconds (displacement3d camera_imu_acs) := imu_msgs.head in
  --ros::Time t(_ros_time_base.toSec() + imu_msg.header.stamp.toSec());
  /-
  The developers now construct a new timestamp for the IMU message first by 
  retrieving "base time" of the "platform"/local system time (which was computed earlier, specifically in the first call to this method (imu_callback_sync)), 
  stored in variable "_ros_time_base", and then converting its value into seconds along with extracting its underlying coordinate via a "toSec" call.
  Next, they retrieve timestamp of imu_msg, stored as "imu_msg.header.stamp" in C++ or "imu_msg.timestamp" in our formalization, 
  whose value is an alias of elapsed_camera_ms, which represents the "offset"/difference 
  between the current hardware/camera timestamp and the "base" of the hardware/camera time (which, again,
  was computed specifically in the first call to this method) with the overall expression expressed in seconds. The coordinates of this object are extracted via the
  "toSec" call. These two coordinates are added together and used as an argument in the construction of the ros::Time object.
  
  We've formalized this by interpreting t as a time expressed in the hardware_time_acs. We bind a value to it by constructing a new
  value of type "time camera_time_seconds" via our mk_time call. The complexity resides in how we compute the coordinates to the new time.

  We define an overload of the "toSec" call for both _ros_time_base and imu_msg.timestamp, whether to provide a global or context-dependent interpretation for 
  toSec is a nuanced issue. Regardless, both overloads of "toSec", "_ros_time_base_toSec" and "_imu_msg_timestamp_toSec", simply extract 
  the respective coordinates of _ros_time_base and _imu_msg_timestamp. Thus, the respective overloads are applied using the respective values, _ros_time_base and _imu_msg_timestamp,
  and the resulting expressions, which have type "scalar", are added together and supplied as an argument to the newly constructed time.

  Note here that, although there is no error here, there should be. The coordinates composing the addition operation hail from two different spaces: platform_time_acs and camera_time_seconds,
  which should yield a type error - as these coordinates hail from different ACSes.
  -/

  let t : time camera_time_seconds :=
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
      --Whether or not to first convert "imu_msg.timestamp" from a time (point) to a duration (vector) should be confirmed by Dr. S
      --let imu_time_as_duration := mk_duration camera_time_seconds imu_msg.timestamp.coord in 
      let _imu_msg_timestamp_toSec : time camera_time_seconds → scalar := 
        λt, 
          t.coord in
      _imu_msg_timestamp_toSec imu_msg.timestamp--imu_time_as_duration
    )) in 
  
  
  punit.star