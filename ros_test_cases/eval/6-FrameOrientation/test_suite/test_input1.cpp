#include "ros/ros.h"
#include "geometry_msgs/Vector3Stamped.h"
#include "geometry_msgs/Vector3.h"
#include "geometry_msgs/Transform.h"
#include "geometry_msgs/TransformStamped.h"
#include <tf/transform_datatypes.h>
#include <tf2_geometry_msgs/tf2_geometry_msgs.h>
#include <tf/transform_listener.h>
#include <tf/transform_broadcaster.h>
//#include "nav_msgs/MapMetaData.h"
//#include "nav_msgs/OccupancyGrid.h"
//#include "nav_msgs/GetMap.h"


#include <cmath>

/*
While trying to create a transform from the World->UTM using an intermediate frame, base link, 
the user accidentally attempts to create World->UTM by composing World->base_link with base_link_yaw_only->UTM. 
This transform happens to be valid, except on a slope where the yaw rotation varies. 
*/
int main(int argc, char **argv){
    ros::init(argc, argv, " ");
    ros::NodeHandle node;  

    /*
    66-83
    
    		mavlink_local_position_ned_t pos_ned;
		mavlink_msg_local_position_ned_decode(msg, &pos_ned);

		ROS_DEBUG_THROTTLE_NAMED(10, "position", "Local position NED: boot_ms:%06d "
				"position:(%1.3f %1.3f %1.3f) speed:(%1.3f %1.3f %1.3f)",
				pos_ned.time_boot_ms,
				pos_ned.x, pos_ned.y, pos_ned.z,
				pos_ned.vx, pos_ned.vy, pos_ned.vz);

		TODO: check convertion to ENU
		 * I think XZY is not body-fixed, but orientation does.
		 * Perhaps this adds additional errorprone to us.
		 * Need more tests. Issue #49.
		 *
		 * orientation in ENU, body-fixed
		 
		tf::Transform transform;
		transform.setOrigin(tf::Vector3(pos_ned.y, pos_ned.x, -pos_ned.z));
    */

    tf::Vector pos_ned;
	tf::Transform transform;

	transform.setOrigin(tf::Vector3(pos_ned.y, pos_ned.x, -pos_ned.z));
}