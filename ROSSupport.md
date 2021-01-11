#Overview
Contains a list of targeted ROS objects and their respective members/conjugations

#Key

#Red means angle implementation is required

##tf::Vector3

- absolute() -> Vector3
- angle(Vector3) -> tfScalar
- closestAxis -> int
- cross(Vector3) -> Vector3

-distance(Vector3) -> Vector3

-distance2(Vector3) -> Vector3

-dot(Vector3) -> Vector3

-furthestAxis() -> int

-getX() -> tfScalar

-getY() -> tfScalar

-getZ() -> tfScalar

-isZero() -> bool

-length() -> tfScalar

-length2() -> tfScalar

-lerp(Vector3,tfScalar) -> Vector3

-maxAxis() -> int

-minAxis() -> int

-normalize() -> Vector3

-normalized() -> Vector3

-rotate(Vector3,tfScalar) -> Vector3

-setMax(Vector3) -> void

-setMin(Vector3) -> void

-setValue(tfScalar,tfScalar,tfScalar) -> void

-setW(tfScalar)

-setX(tfScalar)

-setY(tfScalar)

-setZ(tfScalar)

-setZero()

-triple(Vector3,Vector3)

-w() -> tfScalar

-x() -> tfScalar

-y() -> tfScalar

-z() -> tfScalar

###Operators

-(tfScalar)* -> Vector3

-*=(Vector3) -> Vector3

-+=(Vector3) -> Vector3

--=(Vector3) -> Vector3

-/=(tfScalar) -> Vector3

-==(Vector3) -> bool

###Constructors

-Vector3()
-Vector3(tfScalar,tfScalar,tfScalar)

##tf::Point

Identical to tf::Vector3

##tf::Matrix3x3

###Constructors:
-Matrix3x3
-Matrix3x3(Quaternion)
-Matrix3x3(tfScalar,tfScalar,tfScalar,tfScalar,tfScalar,tfScalar,tfScalar,tfScalar,tfScalar)

###Members
-absolute() -> Matrix3x3
-adjoint() -> Matrix3x3
-cofac(int,int,int,int) -> tfScalar
-derminant() -> tfScalar
-diagonalize() -> void
-getColumn(int) -> Vector3
-getEulerYPR(tfScalar,tfScalar,tfScalar,int) -> void
-getEulerZYX(tfScalar,tfScalar,tfScalar,int) -> void
-getRotation(Quaternion) -> void
-getRow(int) -> Vector3
-getRPY(tfScalar,tfScalar,tfScalar,1) -> void
-inverse() -> Matrix3x3
-scaled(Vector3) -> Matrix3x3
-setFromOpenGLSubMatrix(tfScalar*) -> void
-setIdentity() -> void
-setRotation(Quaternion) -> void
-setRPY(tfScalar,tfScalar,tfScalar) -> void
-setValue(tfScalar,tfScalar,tfScalar,tfScalar,tfScalar,tfScalar,tfScalar,tfScalar,tfScalar) -> void
-timesTranspose(Matrix3x3) -> Matrix3x3
-transpose() -> Matrix3x3

###Operators
-*=(Matrix3x3) -> Matrix3x3
-=(Matrix3x3) -> Matrix3x3
-[int] -> Vector3

###Constructors

-()
-(Quaternion)
-(9x tfScalar)

##tf::Quaternion

-angle(Quaternion) -> tfScalar
-angleShortestPath(Quaternion) -> tfScalar
-dot(Quaternion) -> tfScalar
-farthest(Quaternion) -> Quaternion
-getAngle() -> tfScalar
-getAngleShortestPath() -> tfScalar
-getAxis() -> Vector3
-getW() -> tfScalar
-inverse() -> Quaternion
-length() -> tfScalar
-length2() -> tfScalar
-nearest(Quaternion) -> Quaternion
-normalize() -> Quaternion
-setEuler(tfScalar,tfScalar,tfScalar)
-setEulerZYX(tfScalar,tfScalar,tfScalar)
-setRotation(Vector3,tfScalar)
-setRPY(tfScalar,tfScalar,tfScalar)
-slerp(Quaternion,tfScalar)

###Operators
-*(tfScalar) -> Quaternion
-*=(tfScalar) -> Quaternion
-*=(Quaternion) -> Quaternion
-+(Quaternion) -> Quaternion
-+=(Quaternion) -> Quaternion
--(Quaternion) -> Quaternion
-- -> Quaternion
--=(Quaternion) -> Quaternion
-/(tfScalar) -> Quaternion
-/=(tfScalar) -> Quaternion

###Constructors

-() 
-(tfScalar, tfScalar, tfScalar, tfScalar)
-(Vector3, tfScalar)

##tf::Transform

-getBasis() -> Matrix3x3
-getOrigin() -> Vector3
-getRotation() -> Quaternion
-inverse() -> Transform
-inverseTimes(Transform) -> Transform
-invXform(Vector3) -> Vector3
-mult(Transform,Transform) -> void
-setBasis(Matrix3x3) -> void
-setIdentity() -> void
-setOrigin() -> void
-setRotation(Quaternion) -> Quaternion
-


###Operators

-()(Vector3) -> Vector3
-*(Vector3) -> Vector3
-*(Quaternion) -> Quaternion
-*(Transform) -> Transform
-*=(Transform) -> Transform
-=(Transform) -> Transform

###Constructors
-()
-(Quaternion,Vector3)
-(Matrix3x3,Vector3)

##tfScalar

Alias for float. 

##TransformListener

-transformPoint(targetFrame,Point in, Point out)
-transformPoint(targetFrame,targetTime, Point in, fixedFrame, Point out)
-transformPose(targetFrame,Pose in, Pose out)
-transformPose(targetFrame, targetTime, Pose in, fixedFrame, Pose out)
-transformQuaternion(targetFrame, Quaternion in, Quaternion out)
-transformQuaternion(targetFrame, targetTime, Quaternion in, fixedFrame, Quaternion out)
-transformVector(targetFrame,Vector3 in, Vector3 out)
-transformVector(targetFrame, targetTime, Vector3 in, fixedFrame, Vector3 out)
-lookupTransform(

#Miscellany

-angle(Quaternion,Quaternion) -> tfScalar
-angleShortestPath(Quaternion,Quaternion) -> tfScalar
-assertQuaternionValid(Quaternion)
-assertQuaternionValid(geometry_msgs::Quaternion)
-createIdentityQuaternion() -> Quaternion
-createQuaternionFromRPY(double, double, double) -> Quaternion
-createQuaternionFromYaw(double) -> Quaternion
-createQuaternionMsgFromRollPitchYaw(double, double, double) -> geometry_msgs::Quaternion
-createQuaternionMsgFromYaw(double) -> geometry_msgs::Quaternion
-dot(Quaternion,Quaternion) -> tfScalar
-getYaw(Quaternion) -> double
-getYaw(geometry_msgs::Quaternion) -> double
-inverse(Quaternion) -> Quaternion
-length(Quaternion) -> tfScalar
-lerp(Vector3,Vector3,tfScalar) -> Vector3
-pointMsgToTF(geometry_msgs::Point,Point) -> void
-pointStampedMsgToTF(geometry_msgs::Point,Stamped<Point>) -> void
-pointStampedTFToMsg(Stamped<Point>,geometry_msgs::PointStamped) -> void
-pointTFToMsg(Point,geometry_msgs::Point) -> void
-poseMsgToTF(geometry_msgs::Pose,Pose) -> void
-poseStampedMsgToTF(geometry_msgs::Pose,Stamped<Pose>) -> void
-poseStampedTFToMsg(Stamped<Pose>,geometry_msgs::PoseStamped) -> void
-poseTFToMsg(Pose,geometry_msgs::Pose) -> void
-quaternionMsgToTF(geometry_msgs::Quaternion,Quaternion) -> void
-quaternionStampedMsgToTF(geometry_msgs::Quaternion,Stamped<Quaternion>) -> void
-quaternionStampedTFToMsg(Stamped<Quaternion>,geometry_msgs::QuaternionStamped) -> void
-quaternionTFToMsg(Quaternion,geometry_msgs::Quaternion) -> void
-transformMsgToTF(geometry_msgs::Transform,Transform) -> void
-transformStampedMsgToTF(geometry_msgs::Transform,Stamped<Transform>) -> void
-transformStampedTFToMsg(Stamped<Transform>,geometry_msgs::TransformStamped) -> void
-transformTFToMsg(Transform,geometry_msgs::Transform) -> void
-vector3MsgToTF(geometry_msgs::Vector3,Vector3) -> void
-vector3StampedMsgToTF(geometry_msgs::Vector3,Stamped<Vector3>) -> void
-vector3StampedTFToMsg(Stamped<Vector3>,geometry_msgs::Vector3Stamped) -> void
-vector3TFToMsg(Vector3,geometry_msgs::Vector3) -> void
-quatRotate(Quaternion,Vector3) -> Vector3
-shortestArcQuat(Vector3,Vector3) -> Quaternion
-shortestArcQuatNormalize2(Vector3, Vector3) -> Quaternion
-slerp(Quaternion,Quaternion,tfScalar) -> Quaternion
-tfAngle(Vector3,Vector3) -> tfScalar
-tfCross(Vector3,Vector3) -> Vector3
-tfDistance(Vector3,Vector3) -> tfScalar
-tfDistance2(Vector3,Vector3) -> tfScalar
-tfDot(Vector3,Vector3) -> tfScalar
-tfPlaneSpace1(Vector3,Vector3,Vector3) -> void
-tfTriple(Vector3,Vector3,Vector3) -> tfScalar



#ros::geometry_msgs

-Accel
-AccelStamped
-AccelWithCovariance
-AccelWithCovarianceStamped
-Inertia
-InertiaStamped
-Point
-Point32
-PointStamped
-Polygon
-PolygonStamped
-Pose
-Pose2D
-PoseArray
-PoseStamped
-PoseWithCovariance
-PoseWithCovarianceStamped
-Quaternion
-QuaternionStamped
-Transform
-TransformStamped
-Twist
-TwistStamped
-TwistWithCovariance
-TwistWithCovarianceStamped
-Vector3
-Vector3Stamped
-Wrench
-WrenchStamped

#ros::sensor_msgs
(Skipping a few types in here)

-BatteryState
-CameraInfo
-FluidPressure
-Illuminance
-Imu
-JointState
-LaserEcho
-LaserScan
-MagneticField
-MultiDOFJointState
-MultiEchoLaserScan
-PointCloud
-PointField
-Temperature
-RelativeHumidity
-TimeReference
-JointState

#What Else?
