Issue:
  https://github.com/locusrobotics/fuse/pull/217

TEST 1:

Categorization:

File:
  fuse/fuse_models/include/fuse_models/common/sensor_proc.h

Line:
  line 282

Commit: 8c3738

Code:
  if (target_frame.empty())
        {
            transformed_message = pose;
        }
        else
        {
            transformed_message.header.frame_id = target_frame;

            if (!transformMessage(tf_buffer, pose, transformed_message))
            {
            ROS_ERROR_STREAM("Cannot create constraint from pose message with stamp " << pose.header.stamp);
            return false;
            }
        }

Short Description: 

Error Location/Description: 

Changes in Peirce: 