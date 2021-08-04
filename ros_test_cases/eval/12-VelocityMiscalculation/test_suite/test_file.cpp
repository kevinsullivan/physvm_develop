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
#include <stdlib.h>


#include <cmath>

struct Pose {
float x;
float y;
float yaw;

/**
    * \brief 3x3 covariance matrix in row-major order.
    */
std::vector<float> covariance;
};

typedef Pose Vel;

float getXDistReading(){
    return rand();
}

float getYawReading(){
    return rand();
}

float getDtReading(){
    return rand();
}

int main(int argc, char **argv){
    Vel vel;
    vel.x = getXDistReading()/getDtReading();
    vel.yaw = getYawReading()/getDtReading();
}