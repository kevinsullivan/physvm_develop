5/6/20

- Bad library code may cause to Transformation creation to fail (throws an exception - seen from Trey sample)
- Vectors may get added together - one may not have a frame of reference to even convert to 
- Dynamic vs. Static frames & transformation - both may be a cause of error
- ROS applications often integrate with libraries form external vendors/3rd parties which is a large source of bugs. For example, an update of a camera inverted the z-coordinate in it's reference frame.
