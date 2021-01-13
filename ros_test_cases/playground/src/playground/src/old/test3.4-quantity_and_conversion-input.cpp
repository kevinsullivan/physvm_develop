#include "ros/ros.h"
#include "geometry_msgs/Vector3Stamped.h"
#include "geometry_msgs/Vector3.h"
#include "geometry_msgs/Transform.h"
#include "geometry_msgs/TransformStamped.h"
#include <tf/transform_datatypes.h>
#include <tf2_geometry_msgs/tf2_geometry_msgs.h>
//#include "nav_msgs/MapMetaData.h"
//#include "nav_msgs/OccupancyGrid.h"
//#include "nav_msgs/GetMap.h"

#include <cmath>

/*
Test 3.1

Name - Measurement System Mismatch
Description - 
    Here we try to subtracted two points together that are in different measurement systems.
Expected Outcome - 
    Several spaces are created, along with an SI and Imperial measurement system,
    along with two points in different measurement systems.
    Those points are subtracted to form a vector.
    An error is thrown, as the points belong to two different measurement systems.
Implementation Gaps - 
    Exactly the same set of implementation gaps as Test 3.
  -Layer 1 (Parsers) : 
  -Layer 2 (Peirce) : 
  -Layer 3 (Lang) : 
  -Layer 4 (Phys) : 
  -Layer 5 (CharlieLayer) : 
*/

int main(int argc, char **argv){
    ros::init(argc, argv, "velocity");
    ros::NodeHandle node;  
    ros::console::set_logger_level(ROSCONSOLE_DEFAULT_NAME, ros::console::levels::Debug);

    // GIVEN
    //1 : @@EuclideanGeometry worldGeometry =  EuclideanGeometryLiteral(3)
    //2 : @@ClassicalTime worldTime = ClassicalTimeLiteral()
    //3 : @@ClassicalVelocity worldVelocity = ClassicalVelocityLiteral(worldGeometry, worldTime)
    //4 : @@ClassicalAcceleration worldAcceleration = ClassicalAccelerationLiteral(worldGeometry, worldTime)
    //5 : @@ClassicalGeometryFrame stdWorldFrame = worldGeometry.stdFrame
    //6 : @@MeasurementSystem si = SI()
    //7 : @@MeasurementSystem imp = Imperial()
    //8 : @@ClassicalTimeFrame stdWorldTime = worldTime.stdFrame

    //9 : @@EuclideanGeometryPoint tf_start_point = EuclideanGeometryPoint(worldGeometry,Value=<10,10,10>,stdWorldFrame, si)
    tf::Point
        tf_start_point = tf::Point(10, 10, 10);
    
    //10 : @@EuclideanGeometryPoint tf_end_point = EuclideanGeometryPoint(worldGeometry,Value=<20,-2,12>,stdWorldFrame,si)
    tf::Point
        tf_end_point = tf::Point(20, -2, 12);

    //11 : @@TimePoint now = TimePoint(worldTime,value=<UNK>,stdWorldTime)
    ros::Time now = ros::Time::now();
    //12 : @@TimePoint now_again = TimePoint(worldTime,value=<UNK>,stdWorldTime)
    ros::Time now_again = ros::Time::now();

    //13 : @@TimeVector diff = TimeVector(worldTime,value=<UNK>,stdWorldTime)
    ros::Duration diff = now-now_again;

    //14 : @@TimeQuantity qt = TimeQuantity(worldTime,value=<UNK>)
    tfScalar qt = diff.toSecs();

    //15 (INFERRED?) : @@EuclideanGeometryVector tf_displacement = EuclideanGeometryVector(worldGeometry,Value=<-10,12,-2>,stdWorldFrame, si)
    tf::Vector3 tf_displacement = tf_end_point - tf_start_point;

    //16 : @@ClassicalVelocityFrame stdWorldVel = worldVelocity.stdFrame
    

    //17 : @@ClassicalVelocityVector dps = ClassicalVelocityVector(worldVelocity, Value=<UNK>, stdWorldVel)
    tf::Vector3 = tf_displacement/qt;
}