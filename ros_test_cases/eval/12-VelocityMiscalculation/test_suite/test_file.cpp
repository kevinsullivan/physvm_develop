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

struct Vel {
float x;
float y;
float yaw;

};

typedef Pose Vel;

float getXDistReading(){
    return rand();
}

float getYawReading(){
    return rand();
}

float getTimeReading(){
    return rand();
}

int main(int argc, char **argv){
    float t1 = getTimeReading();
    Vel vel;

    float xdist = getXDistReading();
    float yawdist = getYawReading();

    float t2 = getTimeReading();

    float dt = t2 - t1;

    vel.x = xdist/dt;
    vel.yaw = yawdist/dt;
}