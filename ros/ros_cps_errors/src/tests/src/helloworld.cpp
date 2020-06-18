

#include <vector>
#include "ros/ros.h"
#include "geometry_msgs/Vector3Stamped.h"
#include "geometry_msgs/Vector3.h"
#include "geometry_msgs/Transform.h"
#include "geometry_msgs/TransformStamped.h"
#include <tf/LinearMath/Quaternion.h>
#include <tf/LinearMath/Transform.h>
#include <tf/LinearMath/Vector3.h>
#include <tf/LinearMath/Matrix3x3.h>

#include <tf2_geometry_msgs/tf2_geometry_msgs.h>

#include <tf2_ros/transform_listener.h>

#include <ros/console.h>
#include <boost/shared_ptr.hpp>
#include <boost/thread.hpp>


#include <tf/transform_datatypes.h>
#include <tf/transform_listener.h>

#include <algorithm>
#include <functional>
#include <string>
#include <typeinfo>

std::vector<std::string> tests;

bool check_test_available(std::string test_str){
    return std::find(tests.begin(), tests.end(), test_str) != tests.end();
}

void try_test(std::function<bool(void)> test, std::string name){
    if(check_test_available(name))
        if(test())
            std::remove(tests.begin(), tests.end(), name);
}

//pretend it's an enum
std::string matrix_test = "1"; 
std::string vec_unstamped_test = "2"; 
std::string vec_unstamped_test2 = "2_1"; 
std::string vec_stamped_test = "3"; 
std::string vec_stamped_test2 = "3_1";
std::string pose_unstamped_test = "4"; 
std::string pose_unstamped_test2 = "4_1"; 
std::string pose_stamped_test = "5"; 
std::string pose_stamped_test2 = "5_1";
std::string point_unstamped_test = "6"; 
std::string point_unstamped_test2 = "6_1"; 
std::string point_stamped_test = "7"; 
std::string point_stamped_test2 = "7_1"; 
std::string vec_one_two_listener_valid = "8"; 
std::string vec_one_two_listener_invalid ="9"; 
std::string vec_one_four_static_launch = "10"; 
std::string vec_one_five_static_launch = "11"; 
std::string vec_urdf_one_two = "12"; 
std::string vec_urdf_one_three = "13"; 
std::string pose_one_two_listener_valid = "14"; 
std::string pose_one_two_listener_invalid ="15"; 
std::string pose_one_four_static_launch = "16"; 
std::string pose_one_five_static_launch = "17"; 
std::string pose_urdf_one_two = "18"; 
std::string pose_urdf_one_three = "19"; 
std::string point_one_two_listener_valid = "20"; 
std::string point_one_two_listener_invalid ="21"; 
std::string point_one_four_static_launch = "22"; 
std::string point_one_five_static_launch = "23"; 
std::string point_urdf_one_two = "24"; 
std::string point_urdf_one_three = "25";
std::string transform_unstamped_callback = "26";
std::string listener_test = "27";
std::string buffer_test = "28";
std::string time_test = "29";
std::string dynamic_frame_test = "30";
std::string incorrect_ordering_tests = "31";

void init_tests(){
    tests.push_back(matrix_test);
    tests.push_back(vec_unstamped_test);
    tests.push_back(vec_unstamped_test2);
    tests.push_back(vec_stamped_test);
    tests.push_back(vec_stamped_test2);
    tests.push_back(pose_unstamped_test);
    tests.push_back(pose_unstamped_test2);
    tests.push_back(pose_stamped_test);
    tests.push_back(pose_stamped_test2);
    tests.push_back(point_unstamped_test);
    tests.push_back(point_unstamped_test2);
    tests.push_back(point_stamped_test);
    tests.push_back(point_stamped_test2);
    tests.push_back(vec_one_two_listener_valid);
    tests.push_back(vec_one_two_listener_invalid);
    tests.push_back(vec_one_four_static_launch);
    tests.push_back(vec_one_five_static_launch);
    tests.push_back(vec_urdf_one_two);
    tests.push_back(vec_urdf_one_three);
    tests.push_back(pose_one_two_listener_valid);
    tests.push_back(pose_one_two_listener_invalid);
    tests.push_back(pose_one_four_static_launch);
    tests.push_back(pose_one_five_static_launch);
    tests.push_back(pose_urdf_one_two);
    tests.push_back(pose_urdf_one_three);
    tests.push_back(point_one_two_listener_valid);
    tests.push_back(point_one_two_listener_invalid);
    tests.push_back(point_one_four_static_launch);
    tests.push_back(point_one_five_static_launch);
    tests.push_back(point_urdf_one_two);
    tests.push_back(point_urdf_one_three);
    tests.push_back(listener_test);
    tests.push_back(buffer_test);
    tests.push_back(time_test);
    tests.push_back(dynamic_frame_test);
    tests.push_back(incorrect_ordering_tests);
};

/*

        try_transform_one_to_two_from_listener(one_vec_s,*tfb);//valid
        try_transform_one_to_two_from_listener(two_vec_s, *tfb);//invalid
        try_transform_one_to_four_from_static_launch(one_vec_s, *tfb);//valid
        try_transform_one_to_five_from_static_launch(two_vec_s, *tfb);//invalid

        try_transform_urdf_one_to_two(one_vec_s, *tfb); //valid 
        try_transform_urdf_one_to_three(two_vec_s, *tfb);//invalid

*/


//1. cd to ros_cps_errors directory 
//2. type "catkin_make"
//3. source devel/setup.bash
//4. roslaunch helloworld helloworld.launch

//ROS tainting Eigen data structures?


//store all published messages
std::vector<geometry_msgs::Transform> trans;
std::vector<geometry_msgs::TransformStamped> trans_s;
std::vector<geometry_msgs::Vector3Stamped> vecs_s;
std::vector<geometry_msgs::Vector3> vecs;
std::vector<geometry_msgs::Pose> poses;
std::vector<geometry_msgs::PoseStamped> poses_s;
std::vector<geometry_msgs::Point> points;
std::vector<geometry_msgs::PointStamped> points_s;



void transformCallback(const geometry_msgs::TransformConstPtr& data){
   // ROS_INFO("Buffering transform");
    trans.push_back(*data);
    try_test([=](){
        if(trans.size()>=2){
            tf::Transform onetwo; 
            tf::transformMsgToTF(trans[0], onetwo);//one->two
            tf::Transform onethree; //
            tf::transformMsgToTF(trans[1], onethree);//one->three

            tf::Transform huh = onetwo * onethree;

            ROS_ERROR("Successfully multiplied an UNSTAMPED TF Transform representing one->two with one representing one->three");
            
            tf2::Transform onetwo2; 
            tf2::fromMsg(trans[0], onetwo2);//one->two
            tf2::Transform onethree2; //
            tf2::fromMsg(trans[1], onethree2);//one->three

            tf2::Transform huh2 = onetwo2 * onethree2;

            ROS_ERROR("Successfully multiplied an UNSTAMPED TF2 Transform representing one->two with one representing one->three");

            return true;
        }
        return false;
    }, transform_unstamped_callback);
}

void transformStampedCallback(const geometry_msgs::TransformStampedConstPtr& data){
    //ROS_INFO("Buffering stamped transform");
    trans_s.push_back(*data);
}

void vecCallback(const geometry_msgs::Vector3ConstPtr& data){
    //ROS_INFO("Buffering vector");
    vecs.push_back(*data);
    try_test([=](){
        try{
            if(vecs.size() >= 3)
            {
                //first vec should be in frame one, second should be in frame two

                geometry_msgs::Vector3 new_vec;
                ROS_ERROR("Performing addition with UNSTAMPED vectors initialized in frames one and three");
                new_vec.x = vecs[0].x + vecs[2].x;
                new_vec.y = vecs[0].y + vecs[2].y;
                new_vec.z = vecs[0].z + vecs[2].z;

                
                ROS_DEBUG("Performing addition with UNSTAMPED vectors initialized in frames three and three");
                new_vec.x = vecs[2].x - vecs[2].x;
                new_vec.y = vecs[2].y - vecs[2].y;
                new_vec.z = vecs[2].z - vecs[2].z;
                
                return true;
            }
        }
        catch(std::exception ex){
            ROS_ERROR("%s", ex.what());
        }
        return false;
    }, vec_unstamped_test);
    try_test([=](){
        try{

            if(trans.size() > 2 and vecs.size() > 2){
                geometry_msgs::Vector3 new_vec;
                
                tf::Vector3 v;
                tf::vector3MsgToTF(vecs[1], v);//two
                
                tf::Transform tr;
                tf::transformMsgToTF(trans[1], tr);//one -> two

                tf::Matrix3x3 m = tr.getBasis();
                tf::Vector3 b = tr.getOrigin();

                auto output = tr * v;

                ROS_ERROR("ERROR! Applied an unstamped transform from one to two to an unstamped vector derived from frame two ");
                return true;
            }
        }
        catch(std::exception ex){
            ROS_ERROR("%s", ex.what());
        }
        return false;
    }, vec_unstamped_test2);
}

void vecStampedCallback(const geometry_msgs::Vector3StampedConstPtr& data){
    //ROS_INFO("Buffering vector stamped");
    vecs_s.push_back(*data);
    try_test([=](){
        try{
            if(vecs_s.size() >= 2)
            {
                geometry_msgs::Vector3Stamped new_vec;
                ROS_DEBUG("Performing addition with STAMPED geometry_msg vectors in frames one and one");
                new_vec.vector.x = vecs_s[0].vector.x + vecs_s[0].vector.x;
                new_vec.vector.y = vecs_s[0].vector.y + vecs_s[0].vector.y;
                new_vec.vector.z = vecs_s[0].vector.z + vecs_s[0].vector.z;
                //new_vec = vecs_s[0] + vecs_s[0];
                ROS_ERROR("Performing subtraction with STAMPED geometry_msg vectors in frames one and two");
                new_vec.vector.x = vecs_s[0].vector.x - vecs_s[1].vector.x;
                new_vec.vector.y = vecs_s[0].vector.y - vecs_s[1].vector.y;
                new_vec.vector.z = vecs_s[0].vector.z - vecs_s[1].vector.z;
               // new_vec = vecs_s[]
                ROS_ERROR("Performing multiplication with STAMPED geometry_msg vectors in frames one and two");
                new_vec.vector.x = vecs_s[0].vector.x * vecs_s[1].vector.x;
                new_vec.vector.y = vecs_s[0].vector.y * vecs_s[1].vector.y;
                new_vec.vector.z = vecs_s[0].vector.z * vecs_s[1].vector.z;

                tf::Stamped<tf::Vector3> c0, c1;
                tf::Vector3 c2;
                tf::vector3StampedMsgToTF(vecs_s[0], c0);
                tf::vector3StampedMsgToTF(vecs_s[1], c1);

                ROS_DEBUG("Performing addition with STAMPED tf vectors in frames one and one");
                c2 = c0 + c0;
                //new_vec = vecs_s[0] + vecs_s[0];
                ROS_ERROR("Performing subtraction with STAMPED tf vectors in frames one and two");
                c2 = c0 - c1;
               // new_vec = vecs_s[]
                ROS_ERROR("Performing multiplication with STAMPED tf vectors in frames one and two");
                c2 = c0 * c1;

                tf2::Stamped<tf2::Vector3> c20, c21;
                tf2::Vector3 c22;
                tf2::fromMsg(vecs_s[0], c20);
                tf2::fromMsg(vecs_s[1], c21);

                ROS_DEBUG("Performing addition with STAMPED tf2 vectors in frames one and one");
                c22 = c20 + c20;
                //new_vec = vecs_s[0] + vecs_s[0];
                ROS_ERROR("Performing subtraction with STAMPED tf2 vectors in frames one and two");
                c22 = c20 - c21;
               // new_vec = vecs_s[]
                ROS_ERROR("Performing multiplication with STAMPED tf2 vectors in frames one and two");
                c22 = c20 * c21;

                return true;
            }
        }
        catch(std::exception ex){
            ROS_ERROR("%s", ex.what());
        }
        return false;
    }, vec_stamped_test);
    try_test([=](){
        try{
            if(trans_s.size() > 2 and vecs_s.size() > 1)
            {
                geometry_msgs::Vector3Stamped new_vec;
                //vec_s[1] E "two", trans_s[2] E "one" -> "three"
                ROS_INFO("Attempting to perform a transform on a STAMPED vector in frame two using a STAMPED transform from one to three");
                tf2::doTransform(vecs_s[1], new_vec, trans_s[2]);
                ROS_ERROR("ARG FRAME : %s, TRANSFORM FRAME : %s -> %s, OUT FRAME %s", vecs_s[1].header.frame_id.c_str(), trans_s[2].header.frame_id.c_str(), trans_s[2].child_frame_id.c_str(), new_vec.header.frame_id.c_str());
                return true;
            }
            
        }
        catch(std::exception ex){
            ROS_ERROR("%s", ex.what());
        }
        return false;
    }, vec_stamped_test2);
}


void poseCallback(const geometry_msgs::PoseConstPtr& data){
    poses.push_back(*data);
    try_test([=](){
        try
        {
            if(poses.size() >= 3)
            {
                //first vec should be in frame one, second should be in frame two

                geometry_msgs::Pose new_pose;
                ROS_ERROR("Performing addition with UNSTAMPED poses initialized in frames one and three");
                new_pose.position.x = poses[0].position.x + poses[2].position.x;
                new_pose.position.y = poses[0].position.y + poses[2].position.y;
                new_pose.position.z = poses[0].position.z + poses[2].position.z;

                
                ROS_DEBUG("Performing addition with UNSTAMPED poses initialized in frames three and three");
                new_pose.position.x = poses[2].position.x - poses[2].position.x;
                new_pose.position.y = poses[2].position.y - poses[2].position.y;
                new_pose.position.z = poses[2].position.z - poses[2].position.z;
                return true;
            }
        }
        catch(const std::exception& e)
        {
            ROS_ERROR("%s", e.what());
        }
        return false;
    }, pose_unstamped_test);
    try_test([=](){
        try
        {
            if(trans.size() > 2 and poses.size() > 2){
                geometry_msgs::Pose new_pose;
                
                tf::Pose v;
                tf::poseMsgToTF(poses[1], v);//two
                
                tf::Transform tr;
                tf::transformMsgToTF(trans[1], tr);//one -> two

                tf::Matrix3x3 m = tr.getBasis();
            //  tf::Pose b = tr.getOrigin();

                auto output = tr * v;

                ROS_ERROR("ERROR! Applied an unstamped transform from one to two to an unstamped pose derived from frame two ");

                return true;
            }
        }
        catch(const std::exception& e)
        {
            ROS_ERROR("%s", e.what());
        }
        return false;
    }, pose_unstamped_test2);
}

void poseStampedCallback(const geometry_msgs::PoseStampedConstPtr& data){
    poses_s.push_back(*data);
    try_test([=](){
        try
        {
            if(poses_s.size() >= 2)
            {
                geometry_msgs::PoseStamped new_pose;
                ROS_DEBUG("Performing addition with STAMPED poses in frames one and one");
                new_pose.pose.position.x = poses_s[0].pose.position.x + poses_s[0].pose.position.x;
                new_pose.pose.position.y = poses_s[0].pose.position.y + poses_s[0].pose.position.y;
                new_pose.pose.position.z = poses_s[0].pose.position.z + poses_s[0].pose.position.z;
                ROS_ERROR("Performing subtraction with STAMPED poses in frames one and two");
                new_pose.pose.position.x = poses_s[0].pose.position.x - poses_s[1].pose.position.x;
                new_pose.pose.position.y = poses_s[0].pose.position.y - poses_s[1].pose.position.y;
                new_pose.pose.position.z = poses_s[0].pose.position.z - poses_s[1].pose.position.z;
                ROS_ERROR("Performing multiplication with STAMPED poses in frames one and two");
                new_pose.pose.position.x = poses_s[0].pose.position.x * poses_s[1].pose.position.x;
                new_pose.pose.position.y = poses_s[0].pose.position.y * poses_s[1].pose.position.y;
                new_pose.pose.position.z = poses_s[0].pose.position.z * poses_s[1].pose.position.z;

                return true;
            }
        }
        catch(const std::exception& e)
        {
            ROS_ERROR("%s", e.what());
        }
        return false;
    }, pose_stamped_test);
    try_test([=](){
        try
        {
            if(trans_s.size() > 2 and poses_s.size() > 1)
            {
                geometry_msgs::PoseStamped new_pose;
                //pose_s[1] E "two", trans_s[2] E "one" -> "three"
                ROS_INFO("Attempting to perform a transform on a STAMPED pose in frame two using a STAMPED transform from one to three");
                tf2::doTransform(poses_s[1], new_pose, trans_s[2]);
                ROS_ERROR("ARG FRAME : %s, TRANSFORM FRAME : %s -> %s, OUT FRAME %s", poses_s[1].header.frame_id.c_str(), trans_s[2].header.frame_id.c_str(), trans_s[2].child_frame_id.c_str(), new_pose.header.frame_id.c_str());
                return true;
            }
        }
        catch(const std::exception& e)
        {
            ROS_ERROR("%s", e.what());
        }
        return false;
    }, pose_stamped_test2);
}

void pointCallback(const geometry_msgs::PointConstPtr& data){
    points.push_back(*data);
    try_test([=](){
        try
        {

            if(points.size() >= 3)
            {
                //first point should be in frame one, second should be in frame two

                geometry_msgs::Point new_point;
                ROS_ERROR("Performing addition with UNSTAMPED points initialized in frames one and three");
                new_point.x = points[0].x + points[2].x;
                new_point.y = points[0].y + points[2].y;
                new_point.z = points[0].z + points[2].z;

                
                ROS_DEBUG("Performing addition with UNSTAMPED points initialized in frames three and three");
                new_point.x = points[2].x - points[2].x;
                new_point.y = points[2].y - points[2].y;
                new_point.z = points[2].z - points[2].z;

                return true;
            }
        }
        catch(const std::exception& e)
        {
            ROS_ERROR("%s", e.what());
        }
        return false;
    }, point_unstamped_test);
    try_test([=](){
        try
        {
            if(trans.size() > 2 and points.size() > 2){
                geometry_msgs::Point new_point;
                
                tf::Point v;
                tf::pointMsgToTF(points[1], v);//two
                
                tf::Transform tr;
                tf::transformMsgToTF(trans[1], tr);//one -> two

            // tf::Matrix3x3 m = tr.getBasis();
            // tf::Vector3 b = tr.getOrigin(); <-- ORIGIN IS A VECTOR, NOT A POINT??

                auto output = tr * v;

                ROS_ERROR("ERROR! Applied an unstamped transform from one to two to an unstamped point derived from frame two ");

                return true;
            }
            
        }
        catch(const std::exception& e)
        {
            ROS_ERROR("%s", e.what());
        }
        return false;
    }, point_unstamped_test2);
}

void pointStampedCallback(const geometry_msgs::PointStampedConstPtr& data){

    points_s.push_back(*data);
    try_test([=](){
        try
        {
            if(points_s.size() >= 2)
            {
                geometry_msgs::PointStamped new_point;
                ROS_DEBUG("Performing addition with STAMPED points in frames one and one");
                new_point.point.x = points_s[0].point.x + points_s[0].point.x;
                new_point.point.y = points_s[0].point.y + points_s[0].point.y;
                new_point.point.z = points_s[0].point.z + points_s[0].point.z;
                ROS_ERROR("Performing subtraction with STAMPED points in frames one and two");
                new_point.point.x = points_s[0].point.x - points_s[1].point.x;
                new_point.point.y = points_s[0].point.y - points_s[1].point.y;
                new_point.point.z = points_s[0].point.z - points_s[1].point.z;
                ROS_ERROR("Performing multiplication with STAMPED points in frames one and two");
                new_point.point.x = points_s[0].point.x * points_s[1].point.x;
                new_point.point.y = points_s[0].point.y * points_s[1].point.y;
                new_point.point.z = points_s[0].point.z * points_s[1].point.z;

                return true;
            }
        }
        catch(const std::exception& e)
        {
            ROS_ERROR("%s", e.what());
        }
        return false;
    }, point_stamped_test);
    try_test([=](){
        try
        {
            if(trans_s.size() > 2 and points_s.size() > 1)
            {
                geometry_msgs::PointStamped new_point;
                //point_s[1] E "two", trans_s[2] E "one" -> "three"
                ROS_INFO("Attempting to perform a transform on a STAMPED point in frame two using a STAMPED transform from one to three");
                tf2::doTransform(points_s[1], new_point, trans_s[2]);
                ROS_ERROR("ARG FRAME : %s, TRANSFORM FRAME : %s -> %s, OUT FRAME %s", points_s[1].header.frame_id.c_str(), trans_s[2].header.frame_id.c_str(), trans_s[2].child_frame_id.c_str(), new_point.header.frame_id.c_str());
                return true;
            }
        }
        catch(const std::exception& e)
        {
            ROS_ERROR("%s", e.what());
        }
        return false;
    }, point_stamped_test2);
}

void lookup_and_attempt_transform(geometry_msgs::Vector3Stamped v, const tf2_ros::Buffer& tfb, std::string inframe, std::string outframe){
    try{
        ROS_INFO("%s",("ATTEMPTING TO TRANSFORM VECTOR FROM " + inframe + " TO " + outframe).c_str());
        geometry_msgs::TransformStamped transform;
        transform = tfb.lookupTransform(inframe, outframe, ros::Time(0));
        geometry_msgs::Vector3Stamped new_vec;
        tf2::doTransform(v, new_vec, transform);
        
        if(v.header.frame_id == inframe){
            ROS_DEBUG("ARG FRAME : %s, TRANSFORM FRAME : %s -> %s, OUT FRAME %s", v.header.frame_id.c_str(), transform.header.frame_id.c_str(), transform.child_frame_id.c_str(), new_vec.header.frame_id.c_str());
        }
        else{
            ROS_ERROR("ARG FRAME : %s, TRANSFORM FRAME : %s -> %s, OUT FRAME %s", v.header.frame_id.c_str(), transform.header.frame_id.c_str(), transform.child_frame_id.c_str(), new_vec.header.frame_id.c_str());
        }
    }
    catch(tf2::LookupException& ex){
      ROS_ERROR("ERROR WITH LOOKUP");
      ROS_ERROR("%s",ex.what());
    }
    catch(tf2::TransformException& ex){
      ROS_ERROR("ERROR WITH TRANSFORM");
    }
}

void lookup_and_attempt_transform(geometry_msgs::PointStamped p, const tf2_ros::Buffer& tfb, std::string inframe, std::string outframe){
    try{
        ROS_INFO("%s",("ATTEMPTING TO TRANSFORM POINT FROM " + inframe + " TO " + outframe).c_str());
        geometry_msgs::TransformStamped transform;
        transform = tfb.lookupTransform(inframe, outframe,ros::Time(0));
        geometry_msgs::PointStamped new_pt;
        tf2::doTransform(p, new_pt, transform);
        
        if(p.header.frame_id == inframe){
            ROS_DEBUG("ARG FRAME : %s, TRANSFORM FRAME : %s -> %s, OUT FRAME %s", p.header.frame_id.c_str(), transform.header.frame_id.c_str(), transform.child_frame_id.c_str(), new_pt.header.frame_id.c_str());
        }
        else{
            ROS_ERROR("ARG FRAME : %s, TRANSFORM FRAME : %s -> %s, OUT FRAME %s", p.header.frame_id.c_str(), transform.header.frame_id.c_str(), transform.child_frame_id.c_str(), new_pt.header.frame_id.c_str());
        }
    }
    catch(tf2::LookupException& ex){
      ROS_ERROR("ERROR WITH LOOKUP");
      ROS_ERROR("%s",ex.what());
    }
    catch(tf2::TransformException& ex){
      ROS_ERROR("ERROR WITH TRANSFORM");
    }
}

void lookup_and_attempt_transform(geometry_msgs::PoseStamped p, const tf2_ros::Buffer& tfb, std::string inframe, std::string outframe){
    try{
        ROS_INFO("%s",("ATTEMPTING TO TRANSFORM POSE FROM " + inframe + " TO " + outframe).c_str());
        geometry_msgs::TransformStamped transform;
        transform = tfb.lookupTransform(inframe, outframe,ros::Time(0));
        geometry_msgs::PoseStamped new_pose;
        tf2::doTransform(p, new_pose, transform);
        
        if(p.header.frame_id == inframe){
            ROS_DEBUG("ARG FRAME : %s, TRANSFORM FRAME : %s -> %s, OUT FRAME %s", p.header.frame_id.c_str(), transform.header.frame_id.c_str(), transform.child_frame_id.c_str(), new_pose.header.frame_id.c_str());
        }
        else{
            ROS_ERROR("ARG FRAME : %s, TRANSFORM FRAME : %s -> %s, OUT FRAME %s", p.header.frame_id.c_str(), transform.header.frame_id.c_str(), transform.child_frame_id.c_str(), new_pose.header.frame_id.c_str());
        }
    }
    catch(tf2::LookupException& ex){
      ROS_ERROR("ERROR WITH LOOKUP");
      ROS_ERROR("%s",ex.what());
    }
    catch(tf2::TransformException& ex){
      ROS_ERROR("ERROR WITH TRANSFORM");
    }
}

bool try_lookup_transform(const tf2_ros::Buffer& tfb, geometry_msgs::TransformStamped* tr, std::string inframe, std::string outframe){
    try{
        if(!tr) return false;

        tfb.lookupTransform(inframe, outframe, ros::Time(0));

        return true;
    }
    catch(tf2::LookupException& ex){
      ROS_ERROR("ERROR WITH LOOKUP");
      ROS_ERROR("%s",ex.what());
    }
    catch(tf2::TransformException& ex){
      ROS_ERROR("GENERIC ERROR WITH TRANSFORM");
    }
    return false;
}

//this transform is retrieved from the listener, and published in tf_publisher.
void try_transform_one_to_two_from_listener(geometry_msgs::Vector3Stamped v, const tf2_ros::Buffer& tfb){
    ROS_INFO("ATTEMPTING TRANSFORM ATTEMPT FROM TF BROADCASTER USING STAMPED VECTOR");
    lookup_and_attempt_transform(v, tfb, "one", "two");
    //ROS_INFO("FINISHED TF PUBLISHER LAUNCH ATTEMPT");
}

void try_transform_one_to_two_from_listener(geometry_msgs::PointStamped p, const tf2_ros::Buffer& tfb){
    ROS_INFO("ATTEMPTING TRANSFORM ATTEMPT FROM TF BROADCASTER USING STAMPED POINT");
    lookup_and_attempt_transform(p, tfb, "one", "two");
    //ROS_INFO("FINISHED TF PUBLISHER LAUNCH ATTEMPT");
}

void try_transform_one_to_two_from_listener(geometry_msgs::PoseStamped p, const tf2_ros::Buffer& tfb){
    ROS_INFO("ATTEMPTING TRANSFORM ATTEMPT FROM TF BROADCASTER USING STAMPED POSE");
    lookup_and_attempt_transform(p, tfb, "one", "two");
    //ROS_INFO("FINISHED TF PUBLISHER LAUNCH ATTEMPT");
}

void try_transform_one_to_four_from_static_launch(geometry_msgs::Vector3Stamped v, const tf2_ros::Buffer& tfb){
    ROS_INFO("ATTEMPTING STATIC TRANSFORM FROM LAUNCH FILE USING STAMPED VECTOR");
    lookup_and_attempt_transform(v, tfb, "one", "four");
    //ROS_INFO("FINISHED STATIC LAUNCH ATTEMPT");
}

void try_transform_one_to_four_from_static_launch(geometry_msgs::PointStamped p, const tf2_ros::Buffer& tfb){
    ROS_INFO("ATTEMPTING STATIC TRANSFORM FROM LAUNCH FILE USING STAMPED POINT");
    lookup_and_attempt_transform(p, tfb, "one", "four");
    //ROS_INFO("FINISHED STATIC LAUNCH ATTEMPT");
}

void try_transform_one_to_four_from_static_launch(geometry_msgs::PoseStamped p, const tf2_ros::Buffer& tfb){
    ROS_INFO("ATTEMPTING STATIC TRANSFORM FROM LAUNCH FILE USING STAMPED POSE");
    lookup_and_attempt_transform(p, tfb, "one", "four");
    //ROS_INFO("FINISHED STATIC LAUNCH ATTEMPT");
}

void try_transform_one_to_five_from_static_launch(geometry_msgs::Vector3Stamped v, const tf2_ros::Buffer& tfb){
    ROS_INFO("ATTEMPTING STATIC TRANSFORM FROM LAUNCH FILE USING STAMPED VECTOR");
    lookup_and_attempt_transform(v, tfb, "one", "five");
    //ROS_INFO("FINISHED STATIC LAUNCH ATTEMPT");
}

void try_transform_one_to_five_from_static_launch(geometry_msgs::PointStamped p, const tf2_ros::Buffer& tfb){
    ROS_INFO("ATTEMPTING STATIC TRANSFORM FROM LAUNCH FILE USING STAMPED POINT");
    lookup_and_attempt_transform(p, tfb, "one", "five");
    //ROS_INFO("FINISHED STATIC LAUNCH ATTEMPT");
}

void try_transform_one_to_five_from_static_launch(geometry_msgs::PoseStamped p, const tf2_ros::Buffer& tfb){
    ROS_INFO("ATTEMPTING STATIC TRANSFORM FROM LAUNCH FILE USING STAMPED POSE");
    lookup_and_attempt_transform(p, tfb, "one", "five");
    //ROS_INFO("FINISHED STATIC LAUNCH ATTEMPT");
}


void matrix_tests(){
    try{
        //TAKEN STRAIGHT OUT OF THE DOCUMENTATION:
        //The Transform class supports rigid transforms with only translation and rotation and no scaling/shear. 
        tf::Matrix3x3 test_m(3, 3, 3, 3, 3, 3, 3, 3, 3);

        ROS_ERROR("SUCCESSFULLY INSTANTIATED A HYPOTHETICAL ROTATION MATRIX WITH A NONUNIT DETERMINANT IN TF1");

        tf::Vector3 bias(1, 1, 1);

        tf::Transform invalid_transform(test_m, bias);

        tf::Vector3 output = invalid_transform * bias;

        // INPUT SIZE : 1.732051 , OUTPUT SIZE : 17.320508
        ROS_ERROR("SUCCESSFULLY APPLIED A RIGID BODY TRANSFORM TO A VECTOR USING A SCALING SHEAR");
        ROS_ERROR("INPUT SIZE : %f , OUTPUT SIZE : %f", bias.length(), output.length() );

        
        tf2::Matrix3x3 test_m_2(3, 3, 3, 3, 3, 3, 3, 3, 3);

        ROS_ERROR("SUCCESSFULLY INSTANTIATED A HYPOTHETICAL ROTATION MATRIX WITH A NONUNIT DETERMINANT IN TF2");

        tf2::Vector3 bias_2(1, 1, 1);

        tf2::Transform invalid_transform_2(test_m_2, bias_2);

        tf2::Vector3 output_2 = invalid_transform_2 * bias_2;

        // INPUT SIZE : 1.732051 , OUTPUT SIZE : 17.320508
        ROS_ERROR("SUCCESSFULLY APPLIED A RIGID BODY TRANSFORM TO A VECTOR USING A SCALING SHEAR");
        ROS_ERROR("INPUT SIZE : %f , OUTPUT SIZE : %f", bias_2.length(), output_2.length() );

        tf::Quaternion q1(12, 12, 12, 12);//NOT A ROTATION
        tf::Matrix3x3 rot_quat(q1);
        ROS_ERROR("CREATED A NONUNIT QUATERNION IN TF AND INITIALIZED A ROTATION MATRIX FROM IT");


        tf2::Quaternion q2(12, 12, 12, 12); //not a rotation
        tf2::Matrix3x3 rot_quat2(q2);
        ROS_ERROR("CREATED A NONUNIT QUATERNION IN TF2 AND INITIALIZED A ROTATION MATRIX FROM IT");


        ROS_ERROR("ANDREW NOTE: I believe there is some way to trigger an exception in ROS with a non-unit quaternion, but I can't find it. May possibly be in a custom library.");
    }
    catch(std::exception& ex){
        ROS_ERROR("%s", ex.what());
    }
}

void try_buffer_tests(const tf2_ros::Buffer& tfb, geometry_msgs::PoseStamped one_pose){
    try{
        geometry_msgs::PoseStamped output;

        ROS_INFO("Using the Transform Buffer in TF2 to make a valid transformation from one->two");
        tfb.transform(one_pose, output, "two");

        ROS_INFO("While Transform Buffer is somewhat safer than a raw transform, it cannot guarantee its data is correct");

       // lookup_and_attempt_transform(one_pose, tfb, "one", "eight");

        tfb.transform(one_pose, output, "eight");
        ROS_ERROR("Successfully used an invalid transformation stored in the TF2 Buffer to transform from one->eight");

    }
    catch(std::exception& ex){
        ROS_ERROR("%s", ex.what());
    }
}

void try_listener_tests(const tf::TransformListener& tfl, geometry_msgs::PoseStamped one_pose){
    try{
        geometry_msgs::PoseStamped output;

        ROS_INFO("Using the Transform Listener in TF to make a valid transformation from one->two");
        tfl.transformPose("two", one_pose, output);

        ROS_INFO("While Transform Listener is somewhat safer than a raw transform, it cannot guarantee its data is correct");
        tfl.transformPose("eight", one_pose, output);
        ROS_ERROR("Successfully used an invalid transformation stored in the tf Listener to transform from one->eight");
    }
    catch(std::exception& ex){
        ROS_ERROR("%s", ex.what());
    }
}

void try_transform_urdf_one_to_two(geometry_msgs::Vector3Stamped v, const tf2_ros::Buffer& tfb){
    ROS_INFO("ATEMPTING URDF TRANSFORM");
    lookup_and_attempt_transform(v, tfb, "test_one", "test_two");
    //ROS_INFO("SUCCESSFULLY URDF TRANSFORM FROM ONE TO TWO");
}

void try_transform_urdf_one_to_two(geometry_msgs::PointStamped p, const tf2_ros::Buffer& tfb){
    ROS_INFO("ATEMPTING URDF TRANSFORM WITH STAMPED POINT");
    lookup_and_attempt_transform(p, tfb, "test_one", "test_two");
    //ROS_INFO("SUCCESSFULLY URDF TRANSFORM FROM ONE TO TWO");
}

void try_transform_urdf_one_to_two(geometry_msgs::PoseStamped p, const tf2_ros::Buffer& tfb){
    ROS_INFO("ATEMPTING URDF TRANSFORM WITH STAMPED POSE");
    lookup_and_attempt_transform(p, tfb, "test_one", "test_two");
    //ROS_INFO("SUCCESSFULLY URDF TRANSFORM FROM ONE TO TWO");
}

void try_transform_urdf_one_to_three(geometry_msgs::Vector3Stamped v, const tf2_ros::Buffer& tfb){
    ROS_INFO("ATEMPTING URDF TRANSFORM WITH STAMPED VECTOR");
    lookup_and_attempt_transform(v, tfb, "test_one", "test_three");
    //ROS_INFO("SUCCESSFULLY URDF TRANSFORM FROM ONE TO THREE");
}
void try_transform_urdf_one_to_three(geometry_msgs::PoseStamped p, const tf2_ros::Buffer& tfb){
    ROS_INFO("ATEMPTING URDF TRANSFORM WITH STAMPED POSE");
    lookup_and_attempt_transform(p, tfb, "test_one", "test_three");
    //ROS_INFO("SUCCESSFULLY URDF TRANSFORM FROM ONE TO THREE");
}
void try_transform_urdf_one_to_three(geometry_msgs::PointStamped p, const tf2_ros::Buffer& tfb){
    ROS_INFO("ATEMPTING URDF TRANSFORM WITH STAMPED POINT");
    lookup_and_attempt_transform(p, tfb, "test_one", "test_three");
    //ROS_INFO("SUCCESSFULLY URDF TRANSFORM FROM ONE TO THREE");
}
void try_multiply_one_to_four_and_one_to_five_from_static_launch(const tf2_ros::Buffer& tfb){
    try{
        geometry_msgs::TransformStamped 
            *onefour = new geometry_msgs::TransformStamped(), 
            *onefive = new geometry_msgs::TransformStamped();
        ROS_INFO("Attempting to retrieve transforms one->four and one->five defined statically...");
        if(try_lookup_transform(tfb, onefour, "one", "four") and try_lookup_transform(tfb, onefive, "one", "five")){
            tf::StampedTransform tfOnefour, tfOnefive;
            
            tf::transformStampedMsgToTF(*onefour, tfOnefour);
            tf::transformStampedMsgToTF(*onefive, tfOnefive);

            tf::Transform whoops = tfOnefour * tfOnefive;

            ROS_ERROR("Successfully multiplied together transforms one->four and one->five!! NOTE: A coordinate change is no longer implied by the types");

        }
    }
    catch(std::exception ex){
        ROS_ERROR("%s", ex.what());
    }
}
void time_tests(){
    try{
        ROS_INFO("About to throw an exception....");
        ros::Time t = ros::Time::now();
        ROS_INFO("Current 'now' is: %i", t);
        
        ROS_INFO("Subtracting 1111 seconds from 'now'");
        t.setNow(t + ros::Duration(1111));//ros::Time(0));
        ROS_INFO("Current 'now' is: %i. Confusingly, advances now into the future moves now into the past (and vice versa)", ros::Time::now());
        ROS_INFO("Note: Adding a duration to now will delete all the buffered Transforms. This behavior is not well-documented");

        ROS_INFO("Subtracting two time points");
        ros::Time::now() - ros::Time::now();
        ROS_INFO("Subtracting and Adding a Time point from a Duration (Point +- Vector)");
        t + ros::Duration(5);
        t - ros::Duration(5);
        ROS_INFO("Subtracting and Adding two Durations (Vector +- Vector)");
        ros::Duration(5) + ros::Duration(5);
        ros::Duration(5) - ros::Duration(5);

        ROS_ERROR("Time expression evaluating to a negative time will throw an (unknown) exception");
        ros::Time p = t - ((t - ros::Time(0)) + ros::Duration(10));

    }
    catch(ros::Exception& ex){
        ROS_ERROR("found a ROS exception!!");
        ROS_ERROR("%s", ex.what());
    }
    catch(std::exception ex){
        ROS_ERROR("%s", typeid(ex).name());
        ROS_ERROR("%s", ex.what());
    }
}

void test_dynamic_frames(const tf2_ros::Buffer& tfb){
    geometry_msgs::Vector3Stamped one_vector, prechange, postchange;
    geometry_msgs::PointStamped one_pt, prept, postpt;
    geometry_msgs::TransformStamped old_frame, new_frame;

    one_vector.vector.x = 1;
    one_vector.vector.y = 1;
    one_vector.vector.z = 1;
    one_vector.header.stamp = ros::Time::now();
    one_vector.header.frame_id = "one";

    one_pt.point.x = 1;
    one_pt.point.y = 1;
    one_pt.point.z = 1;
    one_pt.header.stamp = ros::Time::now();
    one_pt.header.frame_id = "one";

   // ros::Duration(1).sleep();
    old_frame = tfb.lookupTransform("one", "ten", ros::Time(0)); //this frame changes over time, as seen in tf broadcaster
   
    tf2::doTransform(one_vector, prechange, old_frame);
    tf2::doTransform(one_pt, prept, old_frame);

    ros::Duration(4).sleep();//wait for frame to update
   
    new_frame = tfb.lookupTransform("one", "ten", ros::Time::now() - ros::Duration(1)); //get the latest version

    ROS_DEBUG("ARG FRAME : %s, TRANSFORM FRAME : %s -> %s, OUT FRAME %s", one_vector.header.frame_id.c_str(), old_frame.header.frame_id.c_str(), old_frame.child_frame_id.c_str(), prechange.header.frame_id.c_str());

    tf2::doTransform(one_vector, postchange, new_frame);
    tf2::doTransform(one_pt, postpt, new_frame);

    ROS_ERROR("Performing a transform on a vector from  one->nine. Failed to update the timestamp on a frame that varies over time. Result for the same vector:");
    ROS_ERROR_STREAM(prechange);
    ROS_ERROR_STREAM(postchange);

    /*
    ROS_INFO("hm?");
    ROS_INFO("%f", one_vector.header.stamp.toSec());
    ROS_INFO("%f", prechange.header.stamp.toSec());
    ROS_INFO("%f", postchange.header.stamp.toSec());
    ROS_INFO("%f", old_frame.header.stamp.toSec());
    ROS_INFO("%f", new_frame.header.stamp.toSec());
    ROS_INFO("%s", one_vector.header.frame_id.c_str());
    ROS_INFO("%s", prechange.header.frame_id.c_str());
    ROS_INFO("%s", postchange.header.frame_id.c_str());
    //auto p = old_frame.rotation;
    ROS_INFO("OLD TRANSFORM");
    ROS_INFO_STREAM(old_frame.transform.rotation);
    ROS_INFO_STREAM(old_frame.transform.translation);
    ROS_INFO("NEW TRANSFORM");
    ROS_INFO_STREAM(new_frame.transform.rotation);
    ROS_INFO_STREAM(new_frame.transform.translation);
    ROS_INFO("VECS");
    ROS_INFO_STREAM(one_vector);
    ROS_INFO_STREAM(prechange);
    ROS_INFO_STREAM(postchange);
    ROS_INFO("POINTS");
    ROS_INFO_STREAM(one_pt);
    ROS_INFO_STREAM(prept);
    ROS_INFO_STREAM(postpt);*/
    

   // ROS_INFO("%f , %f , %f , %f , %f , %s , %s", one_vector.header.stamp , prechange.header.stamp , postchange.header.stamp, old_frame.header.stamp, new_frame.header.stamp, one_vector.header.frame_id.c_str(), prechange.header.frame_id.c_str(), postchange.header.frame_id.c_str() );
}

void test_incorrect_ordering(const tf2_ros::Buffer& tfb){
    ROS_INFO("%s","ATTEMPTING TO TRANSFORM POINT FROM one TO two");
    ROS_INFO("USING THE DOCUMENTED API OF TF2, AN ERROR WILL OCCUR");
    geometry_msgs::TransformStamped transform;
    transform = tfb.lookupTransform("two", "one",ros::Time(0));//using the target, source convention here: http://docs.ros.org/melodic/api/tf2_ros/html/c++/classtf2__ros_1_1Buffer.html#acabbd72cae8f49fb3b6ede3be7e34c55
    geometry_msgs::PointStamped p;
    p.point.x = 1;
    p.point.y = 1;
    p.point.z = 1;
    geometry_msgs::PointStamped new_pt;
    tf2::doTransform(p, new_pt, transform);
    ROS_ERROR("ARG FRAME : %s, TRANSFORM FRAME : %s -> %s, OUT FRAME %s", p.header.frame_id.c_str(), transform.header.frame_id.c_str(), transform.child_frame_id.c_str(), new_pt.header.frame_id.c_str());
    ROS_ERROR("MISSING THE CORRECT TARGET FRAME ON RESULT BY USING THE CORRECT API OF TF");
}

int main(int argc, char **argv)
{
    // Initialize the ROS node and register it with the roscore
    ros::init(argc, argv, "helloworld");
    ros::NodeHandle node;

    init_tests();

    if( ros::console::set_logger_level(ROSCONSOLE_DEFAULT_NAME, ros::console::levels::Debug) )
        ros::console::notifyLoggerLevelsChanged();

    //instantiate listener to lookup transforms that have been broadcast
    boost::shared_ptr<tf2_ros::Buffer> tfb(new tf2_ros::Buffer());
    boost::shared_ptr<tf2_ros::TransformListener> tfl(new tf2_ros::TransformListener(*tfb));
    boost::shared_ptr<tf::TransformListener> tfll(new tf::TransformListener(node));

    auto vec_sub = node.subscribe("/vecs", 25000000, vecCallback);
    auto vec_s_sub = node.subscribe("/vecs_s", 25000000, vecStampedCallback);
    auto transform_sub = node.subscribe("/trans", 25000000, transformCallback);
    auto transform_s_sub = node.subscribe("/trans_s", 25000000, transformStampedCallback);
    auto pose_sub = node.subscribe("/poses", 25000000, poseCallback);
    auto poses_s_sub = node.subscribe("/poses_s", 25000000, poseStampedCallback);
    auto point_sub = node.subscribe("/points", 25000000, pointCallback);
    auto point_s_sub = node.subscribe("/points_s", 25000000, pointStampedCallback);

    
    geometry_msgs::Vector3Stamped one_vec_s;
    one_vec_s.vector.x = 2;
    one_vec_s.vector.y = 2;
    one_vec_s.vector.z = 2;
    one_vec_s.header.frame_id = "one";

    geometry_msgs::Vector3 one_vec;
    one_vec.x = one_vec_s.vector.x;
    one_vec.y = one_vec_s.vector.y;
    one_vec.z = one_vec_s.vector.z;

    geometry_msgs::Vector3Stamped two_vec_s;
    two_vec_s.vector.x = 2;
    two_vec_s.vector.y = 2;
    two_vec_s.vector.z = 2;
    two_vec_s.header.frame_id = "two";

    geometry_msgs::Vector3 two_vec;
    two_vec.x = two_vec_s.vector.x;
    two_vec.y = two_vec_s.vector.y;
    two_vec.z = two_vec_s.vector.z;

    geometry_msgs::PointStamped one_pt_s;
    one_pt_s.point.x = 2;
    one_pt_s.point.y = 2;
    one_pt_s.point.z = 2;
    one_pt_s.header.frame_id = "one";

    geometry_msgs::Point one_pt = one_pt_s.point;

    geometry_msgs::PointStamped two_pt_s;
    two_pt_s.point.x = 2;
    two_pt_s.point.y = 2;
    two_pt_s.point.z = 2;
    two_pt_s.header.frame_id = "two";

    geometry_msgs::Point two_pt = two_pt_s.point;

    tf::Quaternion tqone;
    tqone.setRPY(-1.5, 0, 1.5);
    tf::Quaternion tqtwo;
    tqtwo.setRPY(0,-1.5,1.5);
    tf::Quaternion tqthree;
    tqthree.setRPY(1.5, -1.5, 0);
    geometry_msgs::Quaternion qone, qtwo, qthree;
    tf::quaternionTFToMsg(tqone, qone);
    tf::quaternionTFToMsg(tqtwo, qtwo);
    tf::quaternionTFToMsg(tqthree, qthree);

    geometry_msgs::PoseStamped one_pose_s;
    one_pose_s.pose.position = one_pt;
    one_pose_s.pose.orientation = qone;
    one_pose_s.header.frame_id = "one";

    geometry_msgs::Pose one_pose;
    one_pose.position = one_pt;
    one_pose.orientation = qone;

    geometry_msgs::PoseStamped two_pose_s;
    two_pose_s.pose.position = two_pt;
    two_pose_s.pose.orientation = qtwo;
    two_pose_s.header.frame_id = "two";

    geometry_msgs::Pose two_pose;
    two_pose.position = two_pt;
    two_pose.orientation = qtwo;

    ros::Rate timer(1000);
   // ros::Timer t = node.createTimer(ros::Duration(1), [&](const ros::TimerEvent&){ros::Duration(1000).sleep(); return; });
    boost::thread spin_t{[=](){while(ros::ok() and tests.size() > 0){ros::spinOnce(); ros::Duration(2).sleep();}}};
    while(ros::ok() and tests.size() > 0 )
    {
        timer.sleep();
        ros::Duration(2).sleep();
        //ROS_INFO("Spinning");
        //ros::spinOnce();
        //ROS_INFO("Spun");


        /*VECTOR TESTS*/
        try_test([=](){ try_transform_one_to_two_from_listener(one_vec_s,*tfb); return true; }, vec_one_two_listener_valid);//valid
        try_test([=](){try_transform_one_to_two_from_listener(two_vec_s, *tfb); return true; }, vec_one_two_listener_invalid);//invalid
        try_test([=](){try_transform_one_to_four_from_static_launch(one_vec_s, *tfb); return true; }, vec_one_four_static_launch);//valid
        try_test([=](){try_transform_one_to_five_from_static_launch(two_vec_s, *tfb); return true; }, vec_one_five_static_launch);//invalid

        try_test([=](){try_transform_urdf_one_to_two(one_vec_s, *tfb); return true; }, vec_urdf_one_two); //valid 
        try_test([=](){try_transform_urdf_one_to_three(two_vec_s, *tfb); return true; }, vec_urdf_one_three);//invalid

        
        /*POINT TESTS*/
        try_test([=](){try_transform_one_to_two_from_listener(one_pt_s,*tfb); return true;}, point_one_two_listener_valid);//valid
        try_test([=](){try_transform_one_to_two_from_listener(two_pt_s, *tfb); return true; }, point_one_two_listener_invalid);//invalid
        try_test([=](){try_transform_one_to_four_from_static_launch(one_pt_s, *tfb); return true; }, point_one_four_static_launch);//valid
        try_test([=](){try_transform_one_to_five_from_static_launch(two_pt_s, *tfb); return true; }, point_one_five_static_launch);//invalid

        try_test([=](){try_transform_urdf_one_to_two(one_pt_s, *tfb); return true; }, point_urdf_one_two); //valid 
        try_test([=](){try_transform_urdf_one_to_three(two_pt_s, *tfb); return true; }, point_urdf_one_three);//invalid

        /*POSE TESTS*/
        try_test([=](){try_transform_one_to_two_from_listener(one_pose_s,*tfb); return true; }, pose_one_two_listener_valid);//valid
        try_test([=](){try_transform_one_to_two_from_listener(two_pose_s, *tfb); return true; }, pose_one_two_listener_invalid);//invalid
        try_test([=](){try_transform_one_to_four_from_static_launch(one_pose_s, *tfb); return true; }, pose_one_four_static_launch);//valid
        try_test([=](){try_transform_one_to_five_from_static_launch(two_pose_s, *tfb); return true; }, pose_one_five_static_launch);//invalid

        try_test([=](){try_transform_urdf_one_to_two(one_pose_s, *tfb); return true; }, pose_urdf_one_two); //valid 
        try_test([=](){try_transform_urdf_one_to_three(two_pose_s, *tfb); return true; }, pose_urdf_one_three);//invalid

        
        ros::Duration(4).sleep();
        try_test([=](){matrix_tests(); return true; }, matrix_test);
        try_test([=](){try_listener_tests(*tfll, one_pose_s); return true; }, listener_test);
        try_test([=](){try_buffer_tests(*tfb, one_pose_s); return true; }, buffer_test);
        try_test([=](){test_dynamic_frames(*tfb); return true;}, dynamic_frame_test);
        try_test([=](){test_incorrect_ordering(*tfb); return true;}, incorrect_ordering_tests);
        try_test([=](){time_tests(); return true;}, time_test);

    }
    spin_t.join();

    //Dr Sullivan comment:
    /*
    Annotate this entire piece of code to assume that we are working in geometric space.
    Let the space be called s3d = (p3d, v3d)
    Let f3d be the standard frame on s3d
    f3d = (std_p, std_v_0, std_v_1, std_v_2)

    */
   /*
    geometry_msgs::Vector3Stamped two_vec_s;
    two_vec_s.vector.x = 2;
    two_vec_s.vector.y = 2;
    two_vec_s.vector.z = 2;
    /*
    Let "two" be an affine frame on s3d with coordinates with respect to the std frame
    */
/*
    two_vec_s.header.frame_id = "two";

     //same as in tf_publisher.cpp file
    tf::Quaternion qone;
    qone.setRPY(-1.5, 0, 1.5);
    //{kilometers} -> 
    tf::Vector3 vone(1, 1, 1);//{length, {Real Affine 3 Space, frame two}, vector (not point)}
    tf::Transform tone(qone, vone);//{length, R^3, vector (not point), frame one} -> {length, R^3, vector (not point), frame two}

    geometry_msgs::TransformStamped t3s_one_two;//{length, R^3, vector (not point), frame one} -> {length, R^3, vector (not point), frame two}
    t3s_one_two.header.frame_id = "one";
    t3s_one_two.child_frame_id = "two";
    tf::transformTFToMsg(tone, t3s_one_two.transform);


    geometry_msgs::Vector3Stamped new_vec;//{length, R^3, vector (not point), frame two}
    tf2::doTransform(v, new_vec, transform);//result : {length, R^3, vector (not point), frame one} ! ERROR: frame new_vec <> result of transform
*/

    return 0;
}