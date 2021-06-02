
    // 1. Get the measurement into a tf-friendly transform (pose) object
    tf2::Stamped<tf2::Transform> poseTmp;

    // We'll need this later for storing this measurement for differential integration
    tf2::Transform curMeasurement;

    // Handle issues where frame_id data is not filled out properly
    // @todo: verify that this is necessary still. New IMU handling may
    // have rendered this obsolete.
    std::string finalTargetFrame;
    if (targetFrame == "" && msg->header.frame_id == "")
    {
      // Blank target and message frames mean we can just
      // use our world_frame
      finalTargetFrame = worldFrameId_;
      poseTmp.frame_id_ = finalTargetFrame;
    }
    else if (targetFrame == "")
    {
      // A blank target frame means we shouldn't bother
      // transforming the data
      finalTargetFrame = msg->header.frame_id;
      poseTmp.frame_id_ = finalTargetFrame;
    }
    else
    {
      // Otherwise, we should use our target frame
      finalTargetFrame = targetFrame;
      poseTmp.frame_id_ = (differential && !imuData ? finalTargetFrame : msg->header.frame_id);


template<typename T>
  bool RosFilter<T>::preparePose(const geometry_msgs::PoseWithCovarianceStamped::ConstPtr &msg,
                                 const std::string &topicName,
                                 const std::string &targetFrame,
                                 const bool differential,
                                 const bool relative,
                                 const bool imuData,
                                 std::vector<int> &updateVector,
                                 Eigen::VectorXd &measurement,
                                 Eigen::MatrixXd &measurementCovariance)
  {
    bool retVal = false;

    RF_DEBUG("------ RosFilter::preparePose (" << topicName << ") ------\n");

    // 1. Get the measurement into a tf-friendly transform (pose) object
    tf2::Stamped<tf2::Transform> poseTmp;

    // We'll need this later for storing this measurement for differential integration
    tf2::Transform curMeasurement;

    // Handle issues where frame_id data is not filled out properly
    // @todo: verify that this is necessary still. New IMU handling may
    // have rendered this obsolete.
    std::string finalTargetFrame;
    if (targetFrame == "" && msg->header.frame_id == "")
    {
      // Blank target and message frames mean we can just
      // use our world_frame
      finalTargetFrame = worldFrameId_;
      poseTmp.frame_id_ = finalTargetFrame;
    }
    else if (targetFrame == "")
    {
      // A blank target frame means we shouldn't bother
      // transforming the data
      finalTargetFrame = msg->header.frame_id;
      poseTmp.frame_id_ = finalTargetFrame;
    }
    else
    {
      // Otherwise, we should use our target frame
      finalTargetFrame = targetFrame;
      poseTmp.frame_id_ = (differential && !imuData ? finalTargetFrame : msg->header.frame_id);
    }

    RF_DEBUG("Final target frame for " << topicName << " is " << finalTargetFrame << "\n");

    poseTmp.stamp_ = msg->header.stamp;

    // Fill out the position data
    poseTmp.setOrigin(tf2::Vector3(msg->pose.pose.position.x,
                                   msg->pose.pose.position.y,
                                   msg->pose.pose.position.z));

    tf2::Quaternion orientation;

    // Handle bad (empty) quaternions
    if (msg->pose.pose.orientation.x == 0 && msg->pose.pose.orientation.y == 0 &&
       msg->pose.pose.orientation.z == 0 && msg->pose.pose.orientation.w == 0)
    {
      orientation.setValue(0.0, 0.0, 0.0, 1.0);

      if (updateVector[StateMemberRoll] || updateVector[StateMemberPitch] || updateVector[StateMemberYaw])
      {
        std::stringstream stream;
        stream << "The " << topicName << " message contains an invalid orientation quaternion, " <<
                  "but its configuration is such that orientation data is being used. Correcting...";

        addDiagnostic(diagnostic_msgs::DiagnosticStatus::WARN,
                      topicName + "_orientation",
                      stream.str(),
                      false);
      }
    }
    else
    {
      tf2::fromMsg(msg->pose.pose.orientation, orientation);
      if (fabs(orientation.length() - 1.0) > 0.01)
      {
        ROS_WARN_ONCE("An input was not normalized, this should NOT happen, but will normalize.");
        orientation.normalize();
      }
    }

    // Fill out the orientation data
    poseTmp.setRotation(orientation);

    // 2. Get the target frame transformation
    tf2::Transform targetFrameTrans;
    bool canTransform = RosFilterUtilities::lookupTransformSafe(tfBuffer_,
                                                                finalTargetFrame,
                                                                poseTmp.frame_id_,
                                                                poseTmp.stamp_,
                                                                tfTimeout_,
                                                                targetFrameTrans);

    // 3. Make sure we can work with this data before carrying on
    if (canTransform)
    {
      /* 4. robot_localization lets users configure which variables from the sensor should be
       *    fused with the filter. This is specified at the sensor level. However, the data
       *    may go through transforms before being fused with the state estimate. In that case,
       *    we need to know which of the transformed variables came from the pre-transformed
       *    "approved" variables (i.e., the ones that had "true" in their xxx_config parameter).
       *    To do this, we construct matrices using the update vector values on the diagonals,
       *    pass this matrix through the rotation, and use the length of each row to determine
       *    the transformed update vector. The process is slightly different for IMUs, as the
       *    coordinate frame transform is really the base_link->imu_frame transform, and not
       *    a transform from some other world-fixed frame (even though the IMU data itself *is*
       *    reported in a world fixed frame). */
      tf2::Matrix3x3 maskPosition(updateVector[StateMemberX], 0, 0,
                                  0, updateVector[StateMemberY], 0,
                                  0, 0, updateVector[StateMemberZ]);

      tf2::Matrix3x3 maskOrientation(updateVector[StateMemberRoll], 0, 0,
                                     0, updateVector[StateMemberPitch], 0,
                                     0, 0, updateVector[StateMemberYaw]);

      if (imuData)
      {
        /* We have to treat IMU orientation data differently. Even though we are dealing with pose
         * data when we work with orientations, for IMUs, the frame_id is the frame in which the
         * sensor is mounted, and not the coordinate frame of the IMU. Imagine an IMU that is mounted
         * facing sideways. The pitch in the IMU frame becomes roll for the vehicle. This means that
         * we need to rotate roll and pitch angles by the IMU's mounting yaw offset, and we must apply
         * similar treatment to its update mask and covariance. */

        double dummy, yaw;
        targetFrameTrans.getBasis().getRPY(dummy, dummy, yaw);
        tf2::Matrix3x3 transTmp;
        transTmp.setRPY(0.0, 0.0, yaw);

        maskPosition = transTmp * maskPosition;
        maskOrientation = transTmp * maskOrientation;
      }
      else
      {
        maskPosition = targetFrameTrans.getBasis() * maskPosition;
        maskOrientation = targetFrameTrans.getBasis() * maskOrientation;
      }

      // Now copy the mask values back into the update vector: any row with a significant vector length
      // indicates that we want to set that variable to true in the update vector.
      updateVector[StateMemberX] = static_cast<int>(
        maskPosition.getRow(StateMemberX - POSITION_OFFSET).length() >= 1e-6);
      updateVector[StateMemberY] = static_cast<int>(
        maskPosition.getRow(StateMemberY - POSITION_OFFSET).length() >= 1e-6);
      updateVector[StateMemberZ] = static_cast<int>(
        maskPosition.getRow(StateMemberZ - POSITION_OFFSET).length() >= 1e-6);
      updateVector[StateMemberRoll] = static_cast<int>(
        maskOrientation.getRow(StateMemberRoll - ORIENTATION_OFFSET).length() >= 1e-6);
      updateVector[StateMemberPitch] = static_cast<int>(
        maskOrientation.getRow(StateMemberPitch - ORIENTATION_OFFSET).length() >= 1e-6);
      updateVector[StateMemberYaw] = static_cast<int>(
        maskOrientation.getRow(StateMemberYaw - ORIENTATION_OFFSET).length() >= 1e-6);

      // 5a. We'll need to rotate the covariance as well. Create a container and copy over the
      // covariance data
      Eigen::MatrixXd covariance(POSE_SIZE, POSE_SIZE);
      covariance.setZero();
      copyCovariance(&(msg->pose.covariance[0]), covariance, topicName, updateVector, POSITION_OFFSET, POSE_SIZE);

      // 5b. Now rotate the covariance: create an augmented matrix that
      // contains a 3D rotation matrix in the upper-left and lower-right
      // quadrants, with zeros elsewhere.
      tf2::Matrix3x3 rot;
      Eigen::MatrixXd rot6d(POSE_SIZE, POSE_SIZE);
      rot6d.setIdentity();
      Eigen::MatrixXd covarianceRotated;

      if (imuData)
      {
        // Apply the same special logic to the IMU covariance rotation
        double dummy, yaw;
        targetFrameTrans.getBasis().getRPY(dummy, dummy, yaw);
        rot.setRPY(0.0, 0.0, yaw);
      }
      else
      {
        rot.setRotation(targetFrameTrans.getRotation());
      }

      for (size_t rInd = 0; rInd < POSITION_SIZE; ++rInd)
      {
        rot6d(rInd, 0) = rot.getRow(rInd).getX();
        rot6d(rInd, 1) = rot.getRow(rInd).getY();
        rot6d(rInd, 2) = rot.getRow(rInd).getZ();
        rot6d(rInd+POSITION_SIZE, 3) = rot.getRow(rInd).getX();
        rot6d(rInd+POSITION_SIZE, 4) = rot.getRow(rInd).getY();
        rot6d(rInd+POSITION_SIZE, 5) = rot.getRow(rInd).getZ();
      }

      // Now carry out the rotation
      covarianceRotated = rot6d * covariance * rot6d.transpose();

      RF_DEBUG("After rotating into the " << finalTargetFrame <<
               " frame, covariance is \n" << covarianceRotated <<  "\n");

      /* 6a. For IMU data, the transform that we get is the transform from the body
       * frame of the robot (e.g., base_link) to the mounting frame of the robot. It
       * is *not* the coordinate frame in which the IMU orientation data is reported.
       * If the IMU is mounted in a non-neutral orientation, we need to remove those
       * offsets, and then we need to potentially "swap" roll and pitch.
       * Note that this transform does NOT handle NED->ENU conversions. Data is assumed
       * to be in the ENU frame when it is received.
       * */
      if (imuData)
      {
        // First, convert the transform and measurement rotation to RPY
        // @todo: There must be a way to handle this with quaternions. Need to look into it.
        double rollOffset = 0;
        double pitchOffset = 0;
        double yawOffset = 0;
        double roll = 0;
        double pitch = 0;
        double yaw = 0;
        RosFilterUtilities::quatToRPY(targetFrameTrans.getRotation(), rollOffset, pitchOffset, yawOffset);
        RosFilterUtilities::quatToRPY(poseTmp.getRotation(), roll, pitch, yaw);

        // 6b. Apply the offset (making sure to bound them), and throw them in a vector
        tf2::Vector3 rpyAngles(FilterUtilities::clampRotation(roll - rollOffset),
                               FilterUtilities::clampRotation(pitch - pitchOffset),
                               FilterUtilities::clampRotation(yaw - yawOffset));

        // 6c. Now we need to rotate the roll and pitch by the yaw offset value.
        // Imagine a case where an IMU is mounted facing sideways. In that case
        // pitch for the IMU's world frame is roll for the robot.
        tf2::Matrix3x3 mat;
        mat.setRPY(0.0, 0.0, yawOffset);
        rpyAngles = mat * rpyAngles;
        poseTmp.getBasis().setRPY(rpyAngles.getX(), rpyAngles.getY(), rpyAngles.getZ());

        // We will use this target transformation later on, but
        // we've already transformed this data as if the IMU
        // were mounted neutrall on the robot, so we can just
        // make the transform the identity.
        targetFrameTrans.setIdentity();
      }

      // 7. Two cases: if we're in differential mode, we need to generate a twist
      // message. Otherwise, we just transform it to the target frame.
      if (differential)
      {
        bool success = false;

        // We're going to be playing with poseTmp, so store it,
        // as we'll need to save its current value for the next
        // measurement.
        curMeasurement = poseTmp;

        // Make sure we have previous measurements to work with
        if (previousMeasurements_.count(topicName) > 0 && previousMeasurementCovariances_.count(topicName) > 0)
        {
          // 7a. If we are carrying out differential integration and
          // we have a previous measurement for this sensor,then we
          // need to apply the inverse of that measurement to this new
          // measurement to produce a "delta" measurement between the two.
          // Even if we're not using all of the variables from this sensor,
          // we need to use the whole measurement to determine the delta
          // to the new measurement
          tf2::Transform prevMeasurement = previousMeasurements_[topicName];
          poseTmp.setData(prevMeasurement.inverseTimes(poseTmp));

          RF_DEBUG("Previous measurement:\n" << previousMeasurements_[topicName] <<
                   "\nAfter removing previous measurement, measurement delta is:\n" << poseTmp << "\n");

          // 7b. Now we we have a measurement delta in the frame_id of the
          // message, but we want that delta to be in the target frame, so
          // we need to apply the rotation of the target frame transform.
          targetFrameTrans.setOrigin(tf2::Vector3(0.0, 0.0, 0.0));
          poseTmp.mult(targetFrameTrans, poseTmp);

          RF_DEBUG("After rotating to the target frame, measurement delta is:\n" << poseTmp << "\n");

          // 7c. Now use the time difference from the last message to compute
          // translational and rotational velocities
          double dt = msg->header.stamp.toSec() - lastMessageTimes_[topicName].toSec();
          double xVel = poseTmp.getOrigin().getX() / dt;
          double yVel = poseTmp.getOrigin().getY() / dt;
          double zVel = poseTmp.getOrigin().getZ() / dt;

          double rollVel = 0;
          double pitchVel = 0;
          double yawVel = 0;

          RosFilterUtilities::quatToRPY(poseTmp.getRotation(), rollVel, pitchVel, yawVel);
          rollVel /= dt;
          pitchVel /= dt;
          yawVel /= dt;

          RF_DEBUG("Previous message time was " << lastMessageTimes_[topicName].toSec() <<
                   ", current message time is " << msg->header.stamp.toSec() << ", delta is " <<
                   dt << ", velocity is (vX, vY, vZ): (" << xVel << ", " << yVel << ", " << zVel <<
                   ")\n" << "(vRoll, vPitch, vYaw): (" << rollVel << ", " << pitchVel << ", " <<
                   yawVel << ")\n");

          // 7d. Fill out the velocity data in the message
          geometry_msgs::TwistWithCovarianceStamped *twistPtr = new geometry_msgs::TwistWithCovarianceStamped();
          twistPtr->header = msg->header;
          twistPtr->header.frame_id = baseLinkFrameId_;
          twistPtr->twist.twist.linear.x = xVel;
          twistPtr->twist.twist.linear.y = yVel;
          twistPtr->twist.twist.linear.z = zVel;
          twistPtr->twist.twist.angular.x = rollVel;
          twistPtr->twist.twist.angular.y = pitchVel;
          twistPtr->twist.twist.angular.z = yawVel;
          std::vector<int> twistUpdateVec(STATE_SIZE, false);
          std::copy(updateVector.begin() + POSITION_OFFSET,
                    updateVector.begin() + POSE_SIZE,
                    twistUpdateVec.begin() + POSITION_V_OFFSET);
          std::copy(twistUpdateVec.begin(), twistUpdateVec.end(), updateVector.begin());
          geometry_msgs::TwistWithCovarianceStampedConstPtr ptr(twistPtr);

          // 7e. Now rotate the previous covariance for this measurement to get it
          // into the target frame, and add the current measurement's rotated covariance
          // to the previous measurement's rotated covariance, and multiply by the time delta.
          Eigen::MatrixXd prevCovarRotated = rot6d * previousMeasurementCovariances_[topicName] * rot6d.transpose();
          covarianceRotated = (covarianceRotated.eval() + prevCovarRotated) * dt;
          copyCovariance(covarianceRotated, &(twistPtr->twist.covariance[0]), POSE_SIZE);

          RF_DEBUG("Previous measurement covariance:\n" << previousMeasurementCovariances_[topicName] <<
                   "\nPrevious measurement covariance rotated:\n" << prevCovarRotated <<
                   "\nFinal twist covariance:\n" << covarianceRotated << "\n");

          // Now pass this on to prepareTwist, which will convert it to the required frame
          success = prepareTwist(ptr,
                                 topicName + "_twist",
                                 twistPtr->header.frame_id,
                                 updateVector,
                                 measurement,
                                 measurementCovariance);
        }

        // 7f. Update the previous measurement and measurement covariance
        previousMeasurements_[topicName] = curMeasurement;
        previousMeasurementCovariances_[topicName] = covariance;

        retVal = success;
      }
      else
      {
        // 7g. If we're in relative mode, remove the initial measurement
        if (relative)
        {
          if (initialMeasurements_.count(topicName) == 0)
          {
            initialMeasurements_.insert(std::pair<std::string, tf2::Transform>(topicName, poseTmp));
          }

          tf2::Transform initialMeasurement = initialMeasurements_[topicName];
          poseTmp.setData(initialMeasurement.inverseTimes(poseTmp));
        }

        // 7h. Apply the target frame transformation to the pose object.
        poseTmp.mult(targetFrameTrans, poseTmp);
        poseTmp.frame_id_ = finalTargetFrame;

        // 7i. Finally, copy everything into our measurement and covariance objects
        measurement(StateMemberX) = poseTmp.getOrigin().x();
        measurement(StateMemberY) = poseTmp.getOrigin().y();
        measurement(StateMemberZ) = poseTmp.getOrigin().z();

        // The filter needs roll, pitch, and yaw values instead of quaternions
        double roll, pitch, yaw;
        RosFilterUtilities::quatToRPY(poseTmp.getRotation(), roll, pitch, yaw);
        measurement(StateMemberRoll) = roll;
        measurement(StateMemberPitch) = pitch;
        measurement(StateMemberYaw) = yaw;

        measurementCovariance.block(0, 0, POSE_SIZE, POSE_SIZE) = covarianceRotated.block(0, 0, POSE_SIZE, POSE_SIZE);

        // 8. Handle 2D mode
        if (twoDMode_)
        {
          forceTwoD(measurement, measurementCovariance, updateVector);
        }

        retVal = true;
      }
    }
    else
    {
      retVal = false;

      RF_DEBUG("Could not transform measurement into " << finalTargetFrame << ". Ignoring...");
    }

    RF_DEBUG("\n----- /RosFilter::preparePose (" << topicName << ") ------\n");

    return retVal;
  }