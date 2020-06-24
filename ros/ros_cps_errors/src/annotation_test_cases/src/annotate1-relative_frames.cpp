
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


    /* MAP AND RELATIVE FRAME CONVERSION EXAMPLE */

    // from map server node get map as specified in blank_map.yaml
    // association of "static_map" to map given in launch/annotations.launch
    ros::service::waitForService("/static_map");

    // Get an API client for talking to talking to the map server
    ros::ServiceClient cl = node.serviceClient<nav_msgs::GetMap>("/static_map");

    // Create query to be sent to map service to get interface to get nav occupancy grid
    // Comprising map, meta-data header, including pose of world frame 
    nav_msgs::GetMap gm;

    // Make the call; gm.response then contains result of call
    if(cl.call(gm)){

        // From response get world map (occupancy grid) and frame (pose) for this map
        nav_msgs::OccupancyGrid world_map = gm.response.map;
        //nav_msgs::MapMetaData 
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
       name for this space. Rather, we just get ourselves an affine for it (map_pose).
       Hypothesis: the occupancy grid indicates what's on the floor of a 3-d space, so
       basically where the robot can't go.
       Let's have a look at map_pose on the console.
       */
      
        ROS_INFO("Map Pose : ");
        ROS_INFO_STREAM(map_pose);
       
        /*
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
        */


        /*
        UN-NEEDED FOR THIS EXAMPLE.
        geometry_msgs::TransformStamped map_pose_as_transform;

        map_pose_as_transform.transform.rotation = map_pose.orientation;
        map_pose_as_transform.transform.translation.x = map_pose.position.x;
        map_pose_as_transform.transform.translation.y = map_pose.position.y;
        map_pose_as_transform.transform.translation.z = map_pose.position.z;
        map_pose_as_transform.header = world_map.header;
        */



        /*
        Here, we assume we have the robot's pose from the perspective of the map (world) frame
        Normally, this would be coming in from a sensor, but we define it arbitrarily here.
        */
        geometry_msgs::PoseStamped robot_pose_in_map;
        robot_pose_in_map.header.stamp = ros::Time::now();
        robot_pose_in_map.header.frame_id = world_map.header.frame_id;
        robot_pose_in_map.pose.position.x = 1;
        robot_pose_in_map.pose.position.y = 1;
        robot_pose_in_map.pose.position.z = 1;
        tf::Quaternion map_to_robot_rotation;
        map_to_robot_rotation.setRPY(-1.5, 0, 1.5);
        map_to_robot_rotation.normalize();
        tf::quaternionTFToMsg(map_to_robot_rotation, robot_pose_in_map.pose.orientation);

        
        /*
        Here, we assume we have the robot's left leg from the perspective of the map (world) frame
        Normally, this would be coming in from a sensor, but we define it arbitrarily here.
        */
        geometry_msgs::PoseStamped left_leg_pose_in_map;
        left_leg_pose_in_map.header.stamp = ros::Time::now();
        left_leg_pose_in_map.header.frame_id = world_map.header.frame_id;
        left_leg_pose_in_map.pose.position.x = 2;
        left_leg_pose_in_map.pose.position.y = 2;
        left_leg_pose_in_map.pose.position.z = 2;
        tf::Quaternion map_to_left_leg_rotation;
        map_to_left_leg_rotation.setRPY(-1.5, -1.5, 0);
        map_to_left_leg_rotation.normalize();
        tf::quaternionTFToMsg(map_to_left_leg_rotation, left_leg_pose_in_map.pose.orientation);

        /*
        TF does not allow us to store a Pose, so we generally need to "stuff" a Pose into a Transform in order to manipulate it in TF
        This is acceptable here, however, as we are interesting in using the robot's pose to create a Map Frame -> Robot Frame transform
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
            robot_pose_in_map.header.frame_id,
            "robot_base_link"
        );

        /*
        We prefer to convert the TF transform back into the native geometry_msgs type here, which facilitates easier printing to console,
        of importance in this toy example
        */
        geometry_msgs::TransformStamped map_to_robot_transform;

        tf::transformStampedTFToMsg(tf_map_to_robot_transform, map_to_robot_transform);

        /*
        Convert the robot's pose into the robot frame, which then maps to the origin, by definition of the transform
        */
        geometry_msgs::PoseStamped robot_origin_in_robot_frame;

        tf2::doTransform(robot_pose_in_map, robot_origin_in_robot_frame, map_to_robot_transform);

        ROS_INFO("Assertion : map->robot transform carries the robot pose to the 0 of the child frame");
        ROS_INFO_STREAM(robot_pose_in_map);
        ROS_INFO_STREAM(robot_origin_in_robot_frame);

        /*
        Next, we determine the left leg from the perspective of the robot
        */
        geometry_msgs::PoseStamped left_leg_pose_in_robot;
        tf2::doTransform(left_leg_pose_in_map, left_leg_pose_in_robot, map_to_robot_transform);

        ROS_INFO("Left leg in robot: ");
        ROS_INFO_STREAM(left_leg_pose_in_robot);

        /*
        After that, we can use that perspective to determine the Robot Frame -> Left Leg Frame Transform, similar to before
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

        tf::transformStampedTFToMsg(tf_robot_to_left_leg_transform, robot_to_left_leg_transform);

        tf::StampedTransform tf_left_leg_to_robot_transform(
            tf_robot_to_left_leg_transform.inverse(),
            left_leg_pose_in_robot.header.stamp,
            "robot_left_leg",
            "robot_base_link"
        );

        geometry_msgs::TransformStamped left_leg_to_robot_transform;

        tf::transformStampedTFToMsg(tf_left_leg_to_robot_transform, left_leg_to_robot_transform);

        /*
        As before, the left leg should map to the origin in the left leg frame
        We verify that using an assertion
        */
        geometry_msgs::PoseStamped left_leg_origin_in_left_leg_frame;

        tf2::doTransform(left_leg_pose_in_robot, left_leg_origin_in_left_leg_frame, robot_to_left_leg_transform);

        ROS_INFO("Assertion : robot->left leg transform carries the left leg pose to the 0 of the child frame");
        ROS_INFO_STREAM(left_leg_pose_in_robot);
        ROS_INFO_STREAM(left_leg_origin_in_left_leg_frame);


        /*
            Next, to use the frames that we've established, we'll take a point that is defined and expressed in the perspective of the left leg,
            and we'll determine its value from the perspective of the robot's base link
        */
        geometry_msgs::PointStamped point_in_left_leg, point_in_robot;
        point_in_left_leg.header.frame_id = "robot_left_leg";
        point_in_left_leg.header.stamp = ros::Time::now();
        point_in_left_leg.point.x = 4;
        point_in_left_leg.point.y = 8;
        point_in_left_leg.point.z = 12;

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
