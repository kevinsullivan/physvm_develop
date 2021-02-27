# ROS Units, Coordinates, Frames, Transforms

## Units and Coordinate Conventions

https://www.ros.org/reps/rep-0103.html. 

It notes that "Inconsistency in units and 
conventions is a common source of integration 
issues for developers and can also lead to 
software bugs."

Ros standardizes on the SI unit system. Base
units are meter, kilogram, second, ampere.
Derived units are radian, hertz, newton, watt,
volt, celsius, and tesla.

Coordinate frame conventions vary depending
on intended use, including (forward, left, up),
(east, north, up), (right, down, forward) for
camera suffix frames.

Representations of rotations are several:
quaternion, rotation matrix, roll/pitch/ya,
and Euler angles (and for geograpic coords
east is at yaw=0 increasing counter-clockise,
which differs from the usual compass bearing 
has north at yaw=0 and increases clockwise).

There's more, on covariance matrix reps. See
the documentation.


## Frames and Transforms

https://www.ros.org/reps/rep-0105.html.
"Developers of drivers, models, and libraries
need a share convention for coordinate frames
in order to better integrate and re-use 
software components." An understatement!

ROS uses a number of standardized frames.
- base_link (per vehicle)
- odom (per vehicle)
- map
- earth

More. TBD.
 