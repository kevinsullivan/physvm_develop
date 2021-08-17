import .lang.lang
open lang.time
open lang.geom1d
open lang.geom3d
open lang.series.geom3d
open lang.bool_expr
namespace peirce_output
noncomputable theory


def SyncedImuPublisher : _ := 
  ((
:_))

def ~SyncedImuPublisher : _ := 
  ((
:_))

def Publish : _ := 
  ((
:_))

def Pause : _ := 
  ((
:_))

def Resume : _ := 
  ((
:_))

def PublishPendingMessages : _ := 
  ((
  
:_))

def getNamespaceStr : punit := 


  punit.star

def BaseRealSenseNode : _ := 
  ((
:_))

def ~BaseRealSenseNode : _ := 
  ((
:_))

def toggleSensors : _ → _ := 
  λ enabled, ((
:_))

def setupErrorCallback : _ := 
  ((
:_))

def publishTopics : _ := 
  ((
  setupErrorCallback
:_))

def runFirstFrameInitialization : _ := 
  ((
:_))

def is_checkbox : _ := 
  ((
:_))

def is_enum_option : _ := 
  ((
  let EPSILON : _ := ((_:_)) in
  
  _
:_))

def is_int_option : _ := 
  ((
:_))

def get_enum_method : punit := 


  punit.star

def isValidCharInName : _ := 
  ((
:_))

def create_graph_resource_name : punit := 


  punit.star

def set_auto_exposure_roi : _ := 
  ((
:_))

def set_sensor_auto_exposure_roi : _ := 
  ((
  
:_))

def readAndSetDynamicParam : _ := 
  ((
:_))

def registerAutoExposureROIOptions : _ := 
  ((
:_))

def registerDynamicOption : _ := 
  ((
  
:_))

def registerDynamicReconfigCb : _ := 
  ((
:_))

def rs2_string_to_stream : punit := 


  punit.star

def getParameters : _ := 
  ((
  
  _
  _
  _
  _
  _
  _
  _
  _
  _
  _
  _
  _
  _
  _
  _
  _
  _
  _
  _
  _
:_))

def setupDevice : _ := 
  ((
  
:_))

def setupPublishers : _ := 
  ((
:_))

def publishAlignedDepthToOthers : _ := 
  ((
  
:_))

def enable_devices : _ := 
  ((
:_))

def setupFilters : _ := 
  ((
  let use_disparity_filter : bool_expr := 
    _ in
  let use_colorizer_filter : bool_expr := 
    _ in
  let use_decimation_filter : bool_expr := 
    _ in
  
:_))

def fix_depth_scale : punit := 

  
  

  punit.star

def clip_depth : _ → _ := 
  λ clipping_dist, ((
  
:_))

def CreateUnitedMessage : punit := 

  let t : _ := ((_:_)) in

  punit.star

def FillImuData_LinearInterpolation : _ := 
  ((
  
:_))

def FillImuData_Copy : _ := 
  ((
:_))

def ImuMessage_AddDefaultValues : _ := 
  ((
:_))

def imu_callback_sync : _ := 
  ((
  
  let placeholder_false : bool_expr := 
    _ in
  
:_))

def imu_callback : _ := 
  ((
  
  let placeholder_false : bool_expr := 
    _ in
:_))

def pose_callback : _ := 
  ((
  
  let placeholder_false : bool_expr := 
    _ in
  
  let t : _ := ((_:_)) in
  let pose_msg : _ := ((_:_)) in
  let msg : _ := ((_:_)) in
  let msg0 : _ := |{
    ..msg
  }| in
:_))

def frame_callback : _ := 
  ((
  Pause
  
  Resume
:_))

def multiple_message_callback : _ := 
  ((
:_))

def setBaseTime : _ → _ := 
  λ frame_time, ((
  ((_:_))
:_))

def setupStreams : _ := 
  ((
  
:_))

def updateStreamCalibData : _ := 
  ((
  
:_))

def updateExtrinsicsCalibData : _ := 
  ((
:_))

def rotationMatrixToQuaternion : _ := 
  ((
  ((_:_))
:_))

def publish_static_tf : _ := 
  ((
  let msg : _ := ((_:_)) in
  let msg0 : _ := |{
    ..msg
  }| in
:_))

def calcAndPublishStaticTransform : _ := 
  ((
  let quaternion_optical : _ := ((_:_)) in
  let transform_ts_ : _ := ((_:_)) in
  
  let Q : _ := rotationMatrixToQuaternion in
  ((_:_))
  publish_static_tf ((transform_ts_:_)) ((Q:_))
  publish_static_tf ((transform_ts_:_)) ((quaternion_optical:_))
:_))

def SetBaseStream : _ := 
  ((
  
:_))

def publishStaticTransforms : _ := 
  ((
:_))

def publishDynamicTransforms : _ := 
  ((
  
:_))

def publishIntrinsics : _ := 
  ((
:_))

def reverse_memcpy : _ := 
  ((
  
:_))

def publishPointCloud : _ := 
  ((
  
:_))

def rsExtrinsicsToMsg : punit := 

  

  punit.star

def getAProfile : punit := 


  punit.star

def getImuInfo : punit := 

  
  

  punit.star

def publishFrame : _ → _ := 
  λ copy_data_from_frame, ((
:_))

def getEnabledProfile : _ := 
  ((
  _
:_))

def startMonitoring : _ := 
  ((
:_))

def publish_temperature : _ := 
  ((
:_))

def publish_frequency_update : _ := 
  ((
:_))

def TemperatureDiagnostics : _ := 
  ((
:_))

def diagnostics : _ := 
  ((
:_))



end peirce_output