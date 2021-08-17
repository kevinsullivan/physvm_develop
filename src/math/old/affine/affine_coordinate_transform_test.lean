import .affine_coordinate_framed_space_lib --linear_algebra.affine_space.basic
import 
    linear_algebra.affine_space.basic
    linear_algebra.affine_space.affine_equiv 
    linear_algebra.nonsingular_inverse
    linear_algebra.matrix
    .affine_coordinate_transform

open aff_lib
open aff_fr
open aff_trans

universes u 
variables 
    (K : Type u)
    (n : ℕ )
    [inhabited K]
    [field K]
    (fr1 : affine_coord_frame K n) 
    (fr2 : affine_coord_frame K n) 
    (cv1 cv2 : aff_coord_vec K n fr1) 
    (cp1 cp2 : aff_coord_pt  K n fr2)

variables 
    (fr3 : affine_coord_frame K n)
    (s1 : affine_coord_space K n fr1)
    (s2 : affine_coord_space K n fr2)
    (s3 : affine_coord_space K n fr3)
    (t1 : affine_coord_space_transform K n fr1 fr2 s1 s2)
    (t2 : affine_coord_space_transform K n fr2 fr3 s2 s3)
    (p1 : aff_coord_pt K n fr1)
    (p2 : aff_coord_pt K n fr2)
#check t1⬝t2

#check t1 p1
#check t1 p2  -- There is supposed to be an error here. It means the type-checking is working!
