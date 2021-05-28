affine_space t

# Overview of files

## main abstractions
- affine_space_types        : defines polymorphic affine space type
- affine_with_frame         : defines affine frame type, points and vectors with frames 
- affine_coordinate_space   : exports affine_coordinate_space_type (given X, V, etc)
- affine_coordinate_frame   : defines standard frame for any affine coordinate space
- real_affine_space         : specializes affine coordinate space

## dependencies for the main abstractions
- affine           : defines notation for an affine space
- g_space          : types in which group acts on set leading to torsors
- add_group_action : additive group stuff
- list_stuff       : utility functions on lists to support vector abstractions