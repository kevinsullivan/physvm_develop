Name: Invalid Transform Publication
	Issue: https://github.com/UbiquityRobotics/fiducials/issues/204
	Description: A user discovered that when a transform lookup fails, then control flow continues and the transform gets mistakenly published. Not only that, but the transform appears to be uninitialized (incorrectly initialized) and incorrectly labeled as being from map->base, when it is intended to return a transform of map->odom. Thus, there are multiple modes of failure in this inconsistency. 
	Implementation Challenges: 
	The challenge in implementing this is roughly the same as the issues presented in #2 and #3. The transform can take on multiple values, an option, or a single, incorrect interpretation. At any rate, arguably the most appropriate place to evince an error is here:

The poseTf variable expects to be a assigned a value from map->odom, but, as it may be assigned a value of map->odom, this should trigger an immediate type error in Lean.
	Solution Details:
	We simply need to define a few global annotations such as spaces and what not.