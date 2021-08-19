import .phys.time.time
import .phys.time_series.geom3d
import .std.time_std
import .std.geom3d_std

noncomputable theory


/-
We need to assume a physical interpretation of the data
representing our coordinate system on geom3d. See geom3d_std.lean
for more details on the coordinate system and physical interpretation.
-/
def geometry3d_acs : geom3d_space _ := rice420_acs


/-
We need to assume a physical interpretation of the data
representing our coordinate system on time. We derive a new ACS from 
"coordinated_universal_time_in_seconds" - see time_std.lean 
for a more details on the coordinate system and physical interpretation
(note : this is a conventional UTC ACS expressed with units in seconds)

The gist of this interpretation of our "world time" is that we have formalized
some fixed time at which our application is run, expressed in terms of UTC. 
To do so, we have simply translated the UTC origin to the time at which this was written,
August 18th at ~240 PM. Note: any arbitrary time does not hold any impact on our formal model
(although presumably if we set the origin to the stone age, 
  there should not be a robotics camera running there).
We do not change the basis - which is a standard 
basis whose unit vectors are expressed in seconds.


(1) ORIGIN: We move the origin up to 1629311979

(2) BASIS VECTORS
    basis0 
      - points to the future
      - unit length is 1 second (as in UTC)
      - Presumably no dilation occur, since this is supposed to represent "empirical"
        (atomically-sampled-and-average-weighted) time
(3) ACS is given by [Origin, b0]
-/

def August18thTwoFortyPMTimestamp : scalar := 1629311979

def current_time_in_UTC : time_space _ := 
  let origin := mk_time coordinated_universal_time_in_seconds 1629311979 in
  let basis := mk_duration coordinated_universal_time_in_seconds 1 in
  mk_time_space (mk_time_frame origin basis)


/-
We're assuming a RealSense D435I hardware
unit. It comes with a defined coordinate
system.
We derive from the Rice Hall 420 standard,
aliased in this file as "world_geom_acs".
We'll assume that the camera_imu is two
meters to the right along the back wall,
one meter out from the wall and one meter
high. We'll inhert the standard vector 
space structure from the world_geom_acs.

That's its position in space. As for its
orientation, we'll use the orientation provided
by realsense documentation. In ROS orientation notation,
we might call that 'EDN'

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

We provide an intepretation for the camera's OS clock,
referred to as "System Time" in RealSense nomenclature. 
We are presumably running our application at some "recent" time,
expressed in terms of UTC, so we inherit from the ACS "current_time_in_UTC",
our global intepretation of "world time" - when the "application" is running, in terms of UTC.

This is effectively the camera OS's interpretation of 
what it believes the current UTC time is. 
(https://intelrealsense.github.io/librealsense/doxygen/rs__frame_8h.html#a55750afe3461ea7748fbb2ef6fb19e8a)


We will assume that the origin of the camera OS clock's 
affine coordinate system is off by some delta from the "current time in UTC's" origin, 
which, particularly, is unknowable-statically,
so we're using the "current" origin of the  UTC as the origin Camera's time frame, plus an unspecified delta.

Note that the RealSense API provides sensor dataframes with timestamps expressed in milliseconds - so
our frame is thus expressed in milliseconds as well to reflect that we are consuming this API.

(1) ORIGIN: Some unknown, small constant offset, δ₁, 
away from the origin of the current UTC time's origin,
which reflects the current drift of the clock's origin 

(2) BASIS VECTORS
    basis0 
      - points to the future
      - unit length is 1 millisecond
      - A dilation factor, ε₁, scales the basis vector, 
        to convey the speed of the clock relative to an atomic approximation of UTC time
(3) ACS is given by [Origin, b0]
-/

axiom δ₁ : scalar
axiom ε₁ : scalar

def camera_system_time_acs : time_space _ := 
  let milliseconds := (0.001) in -- SHOULD THIS BE MOVED TO STANDARDS? WHAT SHOULD IT LOOK LIKE?
  let origin := mk_time current_time_in_UTC δ₁ in
  let basis := mk_duration current_time_in_UTC (milliseconds*ε₁) in 
  mk_time_space (mk_time_frame origin basis)

/-

As we must convert from milliseconds (as retrieved through the rs2::Frame API) to seconds,
we express a new ACS which simply conveys the camera_system_time_acs, defined and described just above,
with units in seconds rather than milliseconds.

(1) ORIGIN: The origin is unchanged from camera_system_time_acs

(2) BASIS VECTORS
    basis0 
      - points to the future
      - unit length is 1 second
      - The dilation factor is unchanged from the parent ACS
(3) ACS is given by [Origin, b0]
-/
def camera_system_time_seconds : time_space _ := 
  let milliseconds_to_seconds := 1000 in --MOVE TO STANDARDS? DEFINE WHAT UNITS ARE SOMEWHERE ELSE?
  let origin := mk_time camera_system_time_acs 0 in
  let basis := mk_duration camera_system_time_acs milliseconds_to_seconds in
  mk_time_space (mk_time_frame origin basis)

/-
Next we construct the "hardware time" of the RealSense Camera
(https://intelrealsense.github.io/librealsense/doxygen/rs__frame_8h.html#a55750afe3461ea7748fbb2ef6fb19e8a)
This is a zero-initiated time (it does not reflect the current time in UTC, rather, it conveys how much
time has passed since the camera has begun transmitting data).
 
We define this in terms of UTC time, giving it an origin of 0, with no intrinsic "drift". We share the same
dilation factor as camera_system_time_acs, as we are making the assumption that both of these measurements 
share the same rate of error.

(1) ORIGIN: 0, reflecting that each run of the camera begins at the UTC origin, rather than at the current time

(2) BASIS VECTORS
    basis0 
      - points to the future
      - unit length is 1 millisecond
      - A dilation factor, ε₁, scales the basis vector, 
        to convey the speed of the clock relative to an atomic approximation of UTC time
(3) ACS is given by [Origin, b0]

-/

def camera_hardware_time_acs : time_space _ := 
  let milliseconds := (0.001) in -- SHOULD THIS BE MOVED TO STANDARDS? WHAT SHOULD IT LOOK LIKE?
  let origin := mk_time coordinated_universal_time_in_seconds 0 in
  let basis := mk_duration coordinated_universal_time_in_seconds (milliseconds*ε₁) in 
  mk_time_space (mk_time_frame origin basis)
/-

Similar to the definition of camera_system_time_acs, we define camera_hardware_time_seconds, reflecting the
need to convert from camera_hardware_time_acs (in milliseconds) to an ACS expressed in seconds.

(1) ORIGIN: The origin is unchanged from camera_hardware_time_acs

(2) BASIS VECTORS
    basis0 
      - points to the future
      - unit length is 1 second
      - The dilation factor is unchanged from the parent ACS
(3) ACS is given by [Origin, b0]
-/
def camera_hardware_time_seconds : time_space _ := 
  let milliseconds_to_seconds := 1000 in --MOVE TO STANDARDS? DEFINE WHAT UNITS ARE SOMEWHERE ELSE?
  let origin := mk_time camera_hardware_time_acs 0 in
  let basis := mk_duration camera_hardware_time_acs milliseconds_to_seconds in
  mk_time_space (mk_time_frame origin basis)

/-
This is the ROS client (of the RealSense camera) node's system time, an OS approximation
of the current UTC time expressed in units seconds

One gap to mention here is that this will be used to annotate the system time, which has a native
representation of seconds + nanoseconds, so there is arguably some mismatch when we
annotate the ros::Time variable simply as having units in seconds.

As with our previously-defined camera_system_time_acs, we model a small drift from the origin,
as well as a constant dilation factor to represent the idiosyncratic error of the clock.


(1) ORIGIN: Some unknown, small constant offset, δ₂, 
away from the origin of the current UTC time's origin,
which reflects the current drift of the clock's origin 

(2) BASIS VECTORS
    basis0 
      - points to the future
      - unit length is 1 second
      - A dilation factor, ε₂, scales the basis vector, 
        to convey the speed of the clock relative to an atomic approximation of UTC time


(3) ACS is given by [Origin, b0]
-/

axiom δ₂ : scalar 
axiom ε₂ : scalar

def platform_time_in_seconds := 
  let seconds := 1 in
  let origin := mk_time coordinated_universal_time_in_seconds δ₂ in
  let basis := mk_duration coordinated_universal_time_in_seconds (seconds*ε₂) in 
  mk_time_space (mk_time_frame origin basis)

/-
Lastly formalize the "global time"
(https://intelrealsense.github.io/librealsense/doxygen/rs__frame_8h.html#a55750afe3461ea7748fbb2ef6fb19e8a)
This is a conversion of the "hardware time", adjusted such specifically it's "dilation rate" has been adjusted
from that of the camera's clock to that of a client's clock. Thus, we may think 

This is done in RealSense by a simply linear regression algorithm, and in reality may be subject to some error
if the clock varies over time, but we are only able to model linear relationships, and in this case, 
the necessary conversion reduces to adjusting the hardware's basis by a factor of ε₂/ε₁. 


(1) ORIGIN: The origin is 0, as we are not translating the hardware ACS, just adjusting its dilation factor.

(2) BASIS VECTORS
    basis0 
      - points to the future
      - unit length is 1 millisecond (specified in parent ACS, camera_hardware_time_acs)
      - A dilation factor, ε₂/ε₁, which removes the scaling of the camera's clock, and applies the ROS node's clock dilation


(3) ACS is given by [Origin, b0]
-/
def camera_global_time_acs : time_space _ := 
  let origin := mk_time camera_hardware_time_acs δ₁ in
  let basis := mk_duration camera_hardware_time_acs (ε₂/ε₁) in 
  mk_time_space (mk_time_frame origin basis)

/-

CODE FORMALIZATION OVERVIEW


The parameter of the method imu_callback_sync, "frame", is either timestamped Acceleration or Angular Velocity Vector. 
We have no implementation for either in Peirce (or for sum types for that matter).
Per discussion on last 8/6, this is replaced with a Displacement3D.

We model two versions of this method, reflecting that different sorts of errors can occur. The gap/limitation that causes us to
need to construct two versions of this method is that Peirce, as it is currently constructed, annotates a single execution path. 
Thus, to model two execution paths, we need two versions of formalization. 

In the first instance, we presume that we've received "_camera_time_base" in the camera_hardware_time_acs ACS, 
but that we've just received a dataframe whose timestamp "dataframe.timestamp" domain is expressed in camera_system_time_acs. 
What transpires is that we will subtract two timestamps - "dataframe.timestamp - _camera_time_base", which will yield a type error.
In the actual C++ code, this computation will not yield a type error, 
rather, it will produce an extremely large "change in timestamps" (doubling of the UTC timestamp) which is physically meaningless and can lead to client failures.
The dilation rates + units of the respective ACS's of the operands are compatibile, in this case, but the origins are obviously off by a dramatic amount.

In the second instance, we presume that we've received "_camera_time_base" in the camera_global_time_acs ACS, 
but that we've just received a dataframe whose timestamp "dataframe.timestamp" domain is expressed in camera_hardware_time_acs. 
The only difference from above is that, the error will result in a smaller error - to the tune of a few hundred MS 
(varying over time, as the dilation rates are not in equal in this case).

There are several other others that manifest in either treatment. One is that we annotate a variable suffixed "_ms"
  with a frame expressed in "milliseconds" units, whereas its actual computation is very clearly expressed in seconds. 
  We formalize this such that there is clearly a conversion 
  to (a) seconds (ACS), whereas the variable is typed in (a) milliseconds (ACS), such that a type error manifests. 

Next, when constructing a timestamped datum (CImuData imu_data), the developers are treating a double value which clearly represents a duration, not a
  time, as a timestamp. In our formalization, a type error manifests when constructing the timestamped value.

Lastly, when adding a coordinate from a time expressed in our platform time WITH a coordinate from a time expressed in one of the 
  camera's timestamp domains, there is no error in our formalization (currently - discussed extensively with Dr. Sullivan), 
  although we would like one to be. The specific error that we would like to capture is that, due to differences in dilation rates,
  the addition of _ros_time_base with imu_msg.timestamp (an alias of elapsed_camera_ms), will not produce an accurate timestamp, 
  even when elapsed_camera_ms is computed properly (using matching timestamp domains for both timestamp domains).



void BaseRealSenseNode::imu_callback_sync(rs2::frame dataframe, imu_sync_method sync_method)
-/
def imu_callback_sync_v1 : timestamped camera_system_time_acs (displacement3d camera_imu_acs) → punit := 
  /-
  We define the argument to the method, dataframe. It has an interpretation of 
    timestamped camera_time_acs (displacement3d camera_imu_acs)
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
  let _ros_time_base := mk_time platform_time_in_seconds August18thTwoFortyPMTimestamp in
  let _camera_time_base := mk_time camera_hardware_time_acs 10 in -- 10 is an arbitrary constant
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
  let elapsed_camera_ms : duration camera_system_time_acs
    := (camera_system_time_acs.mk_time_transform_to camera_system_time_seconds).transform_duration ((dataframe_time -ᵥ _camera_time_base : duration camera_system_time_acs)) in
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
  let imu_data : timestamped camera_system_time_seconds (displacement3d camera_imu_acs) := ⟨elapsed_camera_ms, v⟩ in
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

  let imu_msgs : list (timestamped camera_system_time_seconds (displacement3d camera_imu_acs)) := [imu_data] in

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
  let imu_msg : timestamped camera_system_time_seconds (displacement3d camera_imu_acs) := imu_msgs.head in
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

  let t : time camera_system_time_seconds :=
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
      let _imu_msg_timestamp_toSec : time camera_system_time_seconds → scalar := 
        λt, 
          t.coord in
      _imu_msg_timestamp_toSec imu_msg.timestamp--imu_time_as_duration
    )) in 
    /-
    Finally, we update the timestamp of imu_msg with our newly misconstructed time, t
    There is no error at this position.

    imu_msg.header.stamp = t;
    -/
    let imu_msg0 : timestamped camera_system_time_seconds (displacement3d camera_imu_acs) := {
      timestamp := t,
      ..imu_msg
    } in
  
    punit.star

/-

As discussed above, a second version of this method is presented. The only difference is 
that, rather than "_camera_time_base" being in the camera_hardware_time_acs ACS and
"dataframe.timestamp" domain being expressed in the camera_system_time_acs ACS, 
we have "_camera_time_base" being in the camera_global_time_acs ACS and
"dataframe.timestamp" domain being expressed in the camera_hardware_time_acs ACS, which reflects an error
where we have a "time dilation" discrepancy in the subtraction operation, rather than a massive origin mismatch.

The reason, again, for maintaining two versions of the method is due to a limitation in our formalization, in that
we can only express one execution path. Thus, describing a different execution path, in this case inputs with differing
timestamp domains, must be formalized separately.

Verbose comments are omitted from this version - as they only differ in terms of the ACS of the "dataframe" argument to the method
(particularly, the ACS of the timestamp),
as well as the _camera_time_base's type (particularly, the dependent type's ACS value)


void BaseRealSenseNode::imu_callback_sync(rs2::frame dataframe, imu_sync_method sync_method)
-/
def imu_callback_sync_v2 : timestamped camera_hardware_time_acs (displacement3d camera_imu_acs) → punit := 
  λ dataframe, 
  /- 
    double frame_time = frame.get_timestamp();
  -/
  let dataframe_time := dataframe.timestamp in 
  /-setBaseTime(frame_time, frame.get_frame_timestamp_domain());
    _ros_time_base = ros::Time::now();
    _camera_time_base = frame_time;
  -/
  let _ros_time_base := mk_time platform_time_in_seconds August18thTwoFortyPMTimestamp in
  let _camera_time_base := mk_time camera_global_time_acs 10 in -- 10 is an arbitrary constant
--double elapsed_camera_ms = (/*ms*/ frame_time - /*ms*/ _camera_time_base) / 1000.0;
  let elapsed_camera_ms : duration camera_hardware_time_acs
    := (camera_system_time_acs.mk_time_transform_to camera_system_time_seconds).transform_duration ((dataframe_time -ᵥ _camera_time_base : duration camera_system_time_acs)) in
    /-
        auto crnt_reading = *(reinterpret_cast<const float3*>(frame.get_data()));
        Eigen::Vector3d v(crnt_reading.x, crnt_reading.y, crnt_reading.z);
    -/
  let crnt_reading : displacement3d camera_imu_acs := dataframe.value in
  let v : displacement3d camera_imu_acs := mk_displacement3d camera_imu_acs crnt_reading.x crnt_reading.y crnt_reading.z in
  --CimuData imu_data(stream_index, v, elapsed_camera_ms);
  let imu_data : timestamped camera_hardware_time_seconds (displacement3d camera_imu_acs) := ⟨elapsed_camera_ms, v⟩ in
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

  let imu_msgs : list (timestamped camera_hardware_time_seconds (displacement3d camera_imu_acs)) := [imu_data] in

  /-
  
  while (imu_msgs.size())
  {
      sensor_msgs::Imu imu_msg = imu_msgs.front();
  -/
  let imu_msg : timestamped camera_hardware_time_seconds (displacement3d camera_imu_acs) := imu_msgs.head in
  --ros::Time t(_ros_time_base.toSec() + imu_msg.header.stamp.toSec());
  let t : time camera_hardware_time_seconds :=
    mk_time _ 
    ((
      let _ros_time_base_toSec : time platform_time_in_seconds → scalar := 
      λt, 
        (t).coord in
      _ros_time_base_toSec _ros_time_base
    )
    +
    (
      let _imu_msg_timestamp_toSec : time camera_hardware_time_seconds → scalar := 
        λt, 
          t.coord in
      _imu_msg_timestamp_toSec imu_msg.timestamp
    )) in 
    /-
    imu_msg.header.stamp = t;
    -/
    let imu_msg0 : timestamped camera_hardware_time_seconds (displacement3d camera_imu_acs) := {
      timestamp := t,
      ..imu_msg
    } in
  
    punit.star



