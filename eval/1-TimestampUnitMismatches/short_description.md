Issue:
    https://github.com/ros2/geometry2/pull/16

TEST 1:

Categorization: Units of Measurement Mismatch

File:
    test_tf2/test/buffer_core_test.cpp
Line: 635-636 (and more)

Commit:2800f8

Code:
    std::vector<tf2::Duration> durations;
    durations.push_back(tf2::Duration(1.0));//durations.push_back(tf2::durationFromSecond(1.0));

Short Description: The user initializes a vector which he intends will contain values that are expressed in seconds. Due to a misunderstanding of the constructor, while attempting to emplace a value of 1 second, instead emplaces a value of 1 nanosecond.

Code:
    std::vector<tf2::Duration> durations;
    durations.push_back(tf2::Duration(1.0));//durations.push_back(tf2::durationFromSecond(1.0));

Short Description: The user initializes a vector which he intends will contain values that are expressed in seconds. Due to a misunderstanding of the constructor, while attempting to emplace a value of 1 second, instead emplaces a value of 1 nanosecond.

Error Location/Description: There is no error in this case other than the incorrect.

Changes in Peirce: (Possibly) Statically annotating constructors, "List" Constructs which enforce type constraints, Assertions
....

TEST 2:

Categorization: Units of Measurement Mismatch

File:
    tf2_ros/src/tf2_echo.cpp
Line: 105

Commit:2800f8

Categorization: Units of Measurement Mismatch

Code:
    // Wait for up to one second for the first transforms to become avaiable. 
    echoListener.buffer_.canTransform(source_frameid, target_frameid, tf2::TimePoint(), tf2::Duration(1.0));

Short Description: When echoing the coordinates of a transform, tf2 first checks if the transform is available. The timeout to check the transform is intended to be 1 second, but due to a constructor misunderstanding, the user supplies a value of 1 nanosecond.

Error Location/Description: The error is located at the actual code snippet here. In this case, a race condition may ensue if the transform becomes available during the timeout window when the program presumably should have been waiting.

Changes in Peirce: (Possibly) Statically Annotating Constructors, Assertions