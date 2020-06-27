
#include "ros/ros.h"
#include "geometry_msgs/Vector3Stamped.h"
#include "geometry_msgs/Vector3.h"
#include "geometry_msgs/Transform.h"
#include "geometry_msgs/TransformStamped.h"
#include <tf/transform_datatypes.h>
#include <tf2_geometry_msgs/tf2_geometry_msgs.h>
#include "nav_msgs/MapMetaData.h"
#include "nav_msgs/OccupancyGrid.h"
#include "nav_msgs/GetMap.h"


/*
This example creates a simple static model in which a single robot
inhabits a 3-d "map" space; where the map space has a standard frame, 
 "map"; where the robot's base link has a frame, "robot_base_link",
defined in terms of the "map" frame; and where the robot has a single
appendage with its own frame, "robot_left_leg", define in terms of 
the "robot_base_link" frame.

The purpose of this example is to help to drive the design and use
of a system of annotations for annotating such geometric variables
and such, in ROS.

We expect our annotations to include things like the following:

(1) There's a 3D space (the map)
(2) It has a standard frame (defined as the pose of the map, "map")
(3) We define the robot's base link in terms of the standard frame. We use this pose to build a transform,
    implicitly defining the "robot_base_link" frame, to convert coordinates from the robot's perspective to the map's perspective, and vice-versa
(4) We define the robot's left leg in terms of the standard frame. We use this pose and transform it into the previously-established "robot_base_link".
    Next, after the left leg pose is expressed in terms of the base link, we use this to build a transform, implicitly defining the left leg frame,
    which converts coordinates from the left leg's perspective to the robot's perspective, and vice-versa, which can then be used, in conjunction 
    with the transform from step 3, to convert coordinates between the map and left leg frame.
(5) There's some point (that itself needs to be annotated) defined initially in terms of the robot leg frame and we show we can get its coordinates in the base link frame)

*/


int main(int argc, char **argv){
    //Initialize the ROS node and retrieve a handle to it
    ros::init(argc, argv, "relative_frames");   // "annotations" is ROS node name
    ros::NodeHandle node;                   // provides ROS utility functions
    //Allow debug messages to show up in console
    ros::console::set_logger_level(ROSCONSOLE_DEFAULT_NAME, ros::console::levels::Debug);
    /*
    @@
    We're working a 3D Euclidean space, let's call it s3. (Global.)
    Note: s3 comes with a standard frame, let's call it s3.std_frame.
    */
    //@@EuclideanGeometry geometry(dimensions=3);
    //@@Interpret ROS.worldFrame -> geometry.stdFrame=(origin="ScottStadium",frame(chirality=right, unit="m", x="north", y="east", z="up"));
    //@@ClassicalTime time(origin=UTC-origin (1970-01-01T00:00:00Z ISO 8601), unit=second) // minutes are not constant duration in UTC!


    ROS_INFO("Calling initROS (commented out for now");
    //initROS(); 
   // there is a 3D Euclidean world space (implicit in ROS, we make it explicit as "s3").
   // there is a standard frame, the "world frame", on this world space, NED, conventions, standards, ... 
   // we also have a concept of time, including ??? standard frame origin/ephemeric + seconds as a unit?


    /* MAP AND RELATIVE FRAME CONVERSION EXAMPLE */

    // from map server node get map as specified in blank_map.yaml
    // association of "static_map" to map given in launch/annotations.launch
    //We need to make a request to a ROS service that may not be turned on yet, so we wait until it is
    ros::service::waitForService("/static_map");

    // Get an API client for talking to the map server
    ros::ServiceClient cl = node.serviceClient<nav_msgs::GetMap>("/static_map");

    // Create query to be sent to map service to get interface to get nav occupancy grid
    // Comprising map, meta-data header, including pose of world frame 
    nav_msgs::GetMap gm;

    // Make the call; gm.response then contains result of call
    if(cl.call(gm)){

        // From response get world map (occupancy grid) and frame (pose) for this map
        nav_msgs::OccupancyGrid world_map = gm.response.map;
        //nav_msgs::MapMetaData 
        //@@Here we have a tuple of a quaternion and a point expressed in the 3d euclidean world space, s3
        //Both are presented in terms of the world frame, s3.std_frame
        //The point is expressed in units and dimensions meters
        //The quaternion (and quaternions in general) could be annotated as a member of the quaternion group with real scalars, 
        //a set of 3 angles, or as a matrix
        //The quaternions units and dimensions may be expressed in radians?
        /*
        @@Interpret world_map.info.origin as POSE in geometry whose coordinates are ((0, 0, 0),(0, 0, 0, 1)) relative to geometry.stdFrame
        @@Interpret map_pose as POSE in geometry whose coordinates are ((0, 0, 0),(0, 0, 0, 1)) relative to geometry.stdFrame
        */
        geometry_msgs::Pose map_pose = world_map.info.origin;
        //&&Peirce.createWorld()

        /*
        Note that for purposes of this example, the "map" is the world,
        and map_pose is the "world frame".
        "map", the name of this frame, is retrieved from map_server via its /static_map service,
        and it is accessed via world_map.header.frame_id (again, equal to "map")
        */


       /*
       Note: nowhere do we actually instantiate a 3D Euclidean space, nor do we have a
       name for this space. Rather, we just get ourselves an affine frame for it (map_pose).


       Let's have a look at map_pose on the console.
       */
      
        ROS_INFO("Map Pose : ");
        ROS_INFO_STREAM(map_pose);
        /*
        This should look like: 
        [ INFO] [1592857108.938780400]: Map Pose : 
        [ INFO] [1592857108.940042900]: position: 
        x: 0
        y: 0
        z: 0
        orientation: 
        x: 0
        y: 0
        z: 0
        w: 1



        We need help resolving the 2-d occupancy map vs. 3-d Euclidean space in which the
        robot seems to be operating based on the result of the following experiment.

        6/25/20 - This was resolved. map_server should be projected onto R3 via (x, y) -> (x, y, (-inf, inf)). 
        This is not the case for all 2D maps (see https://github.com/ANYbotics/grid_map) 
        */

        /*
        Here, we assume we have the robot's pose from the perspective of the map (world) frame
        Normally, this would be coming in from a sensor/some localization library, but we define it arbitrarily here.
        */
        /*
        @@Again, as before, we have a pose in s3 expressed in terms of the world frame, s3.std_frame
        This pose is composed of a quaternion and a point, each expressed in terms of s3.std_frame

        @@
        */
        
        geometry_msgs::PoseStamped robot_pose_in_map;
        robot_pose_in_map.header.stamp = ros::Time::now();
        robot_pose_in_map.header.frame_id = world_map.header.frame_id;
        //@@To each of the coordinates of the pose's point, we assign a coordinate in s3.std_frame, with units and dimensions in meters 
        robot_pose_in_map.pose.position.x = 1;
        robot_pose_in_map.pose.position.y = 1;
        robot_pose_in_map.pose.position.z = 1;
        
        tf::Quaternion map_to_robot_rotation;
        //@@The quaternion is expressed in terms of 3 angular values in the Euclidean space s3, with units and dimensions in radians
        map_to_robot_rotation.setRPY(-1.5, 0, 1.5);
        map_to_robot_rotation.normalize();
        tf::quaternionTFToMsg(map_to_robot_rotation, robot_pose_in_map.pose.orientation);

        
        /*
        Here, we assume we have the robot's left leg from the perspective of the map (world) frame
        Normally, this would be coming in from a sensor/some localization library, but we define it arbitrarily here.
        */
       /*
        @@Again, as before, we have a pose in s3 expressed in terms of the world frame, s3.std_frame
        This pose is composed of a quaternion and a point, each expressed in terms of s3.std_frame
        */
        
        geometry_msgs::PoseStamped left_leg_pose_in_map;
        left_leg_pose_in_map.header.stamp = ros::Time::now();
        left_leg_pose_in_map.header.frame_id = world_map.header.frame_id;
        //@@To each of the coordinates of the pose's point, we assign a coordinate in s3.std_frame, with units and dimensions in meters 
        left_leg_pose_in_map.pose.position.x = 2;
        left_leg_pose_in_map.pose.position.y = 2;
        left_leg_pose_in_map.pose.position.z = 2;
        tf::Quaternion map_to_left_leg_rotation;
        //@@The quaternion is expressed in terms of 3 angular values in the Euclidean space s3, with units and dimensions in radians
        map_to_left_leg_rotation.setRPY(-1.5, -1.5, 0);
        map_to_left_leg_rotation.normalize();
        tf::quaternionTFToMsg(map_to_left_leg_rotation, left_leg_pose_in_map.pose.orientation);

        /*
        To transform from the map frame to the robot frame, we create a simple change of basis transformation 
        using the robot's pose with respect to the map frame
        */
        //@@We define a Transform that is intended to take objects from s3.std_frame to s3.base_link,
        /*Which is a newly instantiated frame.
        The transform is a translation followed by a rotation. The translation and rotation are defined using the coordinates
        of the robot's pose in the map frame. 
        The dimensions and units of this transform carry points and vectors from meters into meters and take angles from radians into radians
        */
       /*
       a :  transform * robots_pose = (pos:(0, 0, 0),orient:(0,0,0,1)) 
       b:  robots_pose^-1 * robots_pose
       */
      /*
         @@Interpret ROS.robotbaselink -> geometry.stdFrame=(origin="ScottStadium",frame(chirality=right, unit="m", x="north", y="east", z="up"));
    
        GENERAL THOUGHT: tf::Transform what does it do?   
                tf::transform: frame_o x frame_t

      */

        tf::StampedTransform tf_map_to_robot_transform(
            tf::Transform(
                    tf::Quaternion(
                        robot_pose_in_map.pose.orientation.x,
                        robot_pose_in_map.pose.orientation.y,
                        robot_pose_in_map.pose.orientation.z,
                        robot_pose_in_map.pose.orientation.w
                    ),
                    tf::Vector3(
                        robot_pose_in_map.pose.position.x,
                        robot_pose_in_map.pose.position.y,
                        robot_pose_in_map.pose.position.z
                    )
                ).inverse(),
            robot_pose_in_map.header.stamp,
            robot_pose_in_map.header
        );.frame_id,
            "robot_base_link"

        /*
        We prefer to convert the TF transform back into the native geometry_msgs type here, which facilitates easier printing to console,
        of importance in this example
        */
       /*
        @@This is nothing more than an assignment operation from tf_map_to_robot_transform, so we are propagating
        tf_map_to_robot_transform's annotations onto map_to_robot_transform. Thus,
        it is a transform from s3.std_frame to s3.base_link, defined relative to the pose of the robot, 
        and dimensions and units of this transform carry points and vectors from meters into meters and take angles from radians into radians
       */
        geometry_msgs::TransformStamped map_to_robot_transform;

        tf::transformStampedTFToMsg(tf_map_to_robot_transform, map_to_robot_transform);

        /*
        Convert the robot's pose into the robot frame, which then maps to the origin, by definition of the transform
        */

        geometry_msgs::PoseStamped robot_origin_in_robot_frame;
        /*
        @@We store the result of map_to_robot_transform(robot_pose_in_map) into robot_origin_in_robot_frame.
        The input, robot_pose_in_map, honors the input specificatoin of map_to_robot_transform, so the transformation application is physically meaningful
        This implies that robot_origin_in_robot_frame is in s3.base_link, and that its orientation is in radians (if the quaternion is represented that way)
        and that its position is in meters
        */
        tf2::doTransform(robot_pose_in_map, robot_origin_in_robot_frame, map_to_robot_transform);

        ROS_INFO("Assertion : map->robot transform carries the robot pose to the 0 of the child frame");
        ROS_INFO_STREAM(robot_pose_in_map);
        ROS_INFO_STREAM(robot_origin_in_robot_frame);
        /*
         robot_origin_in_robot_frame:
        position 0, 0, 0
        orientation 0, 0, 0, 1
        */

        /*
        Next, we determine the left leg from the perspective of the robot
        */
        /*
        @@Exactly as in the prior transformation result, we check the result of left_leg_pose_in_robot = map_to_robot_transform(left_leg_pose_in_map)
        which, again, is physically meaningful. 
        The result puts the pose's position in s3.base_link expressed in meters, and its orientation is in (possibly) radians
        */
        geometry_msgs::PoseStamped left_leg_pose_in_robot;
        tf2::doTransform(left_leg_pose_in_map, left_leg_pose_in_robot, map_to_robot_transform);

        ROS_INFO("Left leg in robot: ");
        ROS_INFO_STREAM(left_leg_pose_in_robot);

        /*
        After that, we can use that perspective to determine the Robot Frame -> Left Leg Frame Transform, similar to before
        We need to use the robot's left leg in terms of the robot's base link, instead of the map frame
        */
        /*
        @@Here we use a pose, left_leg_pose_in_robot, 
        expressed in terms of s3.base_link to define a transform to a new frame, s3.left_leg, which is defined in terms of the pose
        The transform has dimensions and units of this transform carry points and vectors from meters into meters and take angles from radians into radians
        */
        tf::StampedTransform tf_robot_to_left_leg_transform(
            tf::Transform(
                    tf::Quaternion(
                        left_leg_pose_in_robot.pose.orientation.x,
                        left_leg_pose_in_robot.pose.orientation.y,
                        left_leg_pose_in_robot.pose.orientation.z,
                        left_leg_pose_in_robot.pose.orientation.w
                    ),
                    tf::Vector3(
                        left_leg_pose_in_robot.pose.position.x,
                        left_leg_pose_in_robot.pose.position.y,
                        left_leg_pose_in_robot.pose.position.z
                    )
                ).inverse(),
            left_leg_pose_in_robot.header.stamp,
            left_leg_pose_in_robot.header.frame_id,
            "robot_left_leg"
        );

        /*
        Again, we prefer to work in native geometry_msgs here
        */
        geometry_msgs::TransformStamped robot_to_left_leg_transform;// = tf_map_to_robot_transform.toMsg();
        /*
        @@This is a simple assignment of the transform defined in tf_robot_to_left_leg_transform to robot_to_left_leg_transform
        Thus, robot_to_left_leg_transform now represents a transform from s3.robot_base to s3.left_leg, and 
        the dimensions and units of this transform carry points and vectors from meters into meters and take angles from radians into radians
        */
        tf::transformStampedTFToMsg(tf_robot_to_left_leg_transform, robot_to_left_leg_transform);

        /*
        @@We define a transform in terms of the inverse of tf_robot_to_left_leg_transform. Thus, tf_left_leg_to_robot_transform
        must transform from s3.left_leg to s3.robot_base. 
        Again, the dimensions and units of this transform carry points and vectors from meters into meters and take angles from radians into radians
        */
        tf::StampedTransform tf_left_leg_to_robot_transform(
            tf_robot_to_left_leg_transform.inverse(),
            left_leg_pose_in_robot.header.stamp,
            "robot_left_leg",
            "robot_base_link"
        );

        geometry_msgs::TransformStamped left_leg_to_robot_transform;
        //
        /*
        @@This is a simple assignment of the inverse transform defined in tf_left_leg_to_robot_transform to left_leg_to_robot_transform
        Thus, left_leg_to_robot_transform now represents a transform from s3.left_leg to s3.robot_base, and 
        the dimensions and units of this transform carry points and vectors from meters into meters and take angles from radians into radians
        */
        tf::transformStampedTFToMsg(tf_left_leg_to_robot_transform, left_leg_to_robot_transform);

        /*
        The left leg in presented in the robot frame should get mapped to the origin in the left leg frame using our transform
        We verify that using an assertion
        */
        geometry_msgs::PoseStamped left_leg_origin_in_left_leg_frame;

        /*
        @@We store the result of robot_to_left_leg_transform(left_leg_pose_in_robot) into left_leg_origin_in_left_leg_frame.
        The input, left_leg_pose_in_robot, honors the input specificatoin of robot_to_left_leg_transform, so the transformation application is physically meaningful
        This implies that left_leg_origin_in_left_leg_frame is in s3.left_leg, and that its orientation is in radians (if the quaternion is represented that way)
        and that its position is in meters
        */
        tf2::doTransform(left_leg_pose_in_robot, left_leg_origin_in_left_leg_frame, robot_to_left_leg_transform);

        ROS_INFO("Assertion : robot->left leg transform carries the left leg pose to the 0 of the child frame");
        ROS_INFO_STREAM(left_leg_pose_in_robot);
        ROS_INFO_STREAM(left_leg_origin_in_left_leg_frame);


        /*
            Next, to use the frames that we've established, we'll take a point that is defined and expressed in the perspective of the left leg,
            and we'll determine its value from the perspective of the robot's base link
        */
        /*
        Here we define an arbitrary point, point_in_left_leg, in s3, which is presented in s3.robot_left_leg
        It has dimensions and units in meters
        */
        geometry_msgs::PointStamped point_in_left_leg, point_in_robot;
        point_in_left_leg.header.frame_id = "robot_left_leg";
        point_in_left_leg.header.stamp = ros::Time::now();
        //@@We assign a coordinate of the coordinate space s3, which are each expressed in meters
        point_in_left_leg.point.x = 4;
        point_in_left_leg.point.y = 8;
        point_in_left_leg.point.z = 12;

        /*
        @@We store the result of left_leg_to_robot_transform(point_in_left_leg) into point_in_robot.
        The input, point_in_left_leg, honors the input specification of left_leg_to_robot_transform, so the transformation application is physically meaningful
        This implies that point_in_robot is in s3.robot_base, and that its orientation is in radians (if the quaternion is represented that way)
        and that its position is in meters
        */
        tf2::doTransform(point_in_left_leg, point_in_robot, left_leg_to_robot_transform);

        ROS_INFO("Point in Robot Left Leg : ");
        ROS_INFO_STREAM(point_in_left_leg);

        ROS_INFO("Point in Robot Base Link : ");
        ROS_INFO_STREAM(point_in_robot);
    }
    else{
        ROS_DEBUG("Failed to call service!");
    }
    
    /* MAP AND RELATIVE FRAME CONVERSION EXAMPLE */
}
