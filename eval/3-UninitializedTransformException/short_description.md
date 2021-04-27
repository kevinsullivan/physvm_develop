Issue:
	https://github.com/ros-perception/ar_track_alvar/pull/79

TEST 1:

Categorization: Invalid Transform Usage

File:
	ar_tar_alvar/nodes/IndividualMarkersNoKinect.cpp

Line: 88

Commit:
	ebb782

Code:
    			try{
					tf_listener->waitForTransform(output_frame, image_msg->header.frame_id, image_msg->header.stamp, ros::Duration(1.0));
					tf_listener->lookupTransform(output_frame, image_msg->header.frame_id, image_msg->header.stamp, CamToOutput);
   				}
    			catch (tf::TransformException ex){
      				ROS_ERROR("%s",ex.what());
    			}

Short Description: A try catch block is used when trying to look up a transform, as is typical in ROS, however, if it fails to lookup the transform, execution does not stop, and this faulty transform is used. As even a minor deviation in a transform from its correct value can result in drastically different output than what is expected, this is an error.

Error Location/Description: An error state occurs on line 200, when we attempt to use the invalid transform to transform a pose in the Camera Frame to the Output Frame

Changes in Peirce: 
	In the simplest case, nothing
	Possibly control flow, 
	Various Approaches to annotating the Transform:Sets (I believe more scalable), Options,
	Assertions