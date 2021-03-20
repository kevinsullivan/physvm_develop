import linear_algebra.affine_space.basic
import data.real.basic

abbreviation value_isomorphism_torsor := { x:ℝ // x>0 } 

abbreviation scale_transformation_group := { x:ℝ // x>0 } 

instance : add_comm_group scale_transformation_group := sorry

abbreviation value_torsor_over_scale_transformation := add_torsor value_isomorphism_torsor scale_transformation_group

instance : add_torsor value_isomorphism_torsor scale_transformation_group := sorry
