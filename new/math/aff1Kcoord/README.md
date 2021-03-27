# The Affine1K Library

To use this library, import aff1Kcoord_std. This module provides a 1-D affine K coordinate space with points and vectors respectively each having their single (1-D) coordinates from a field, K.

- (std_space K) is a 1-D affine space with K vectors and K points.
- instantiate points in std_space using (mk_point (std_spc K) k)
- instantiate vectors in std_space using (mk_vectr (std_spc K) k) 
- use points and vectors to instantiate new frame: mk_frame (<point>) (<vectr>)
- establish new coordinate space based on frame: (mk_space K new_frame)

Within any affine coordinate space, you have points, vectors, vector space operations 
(vector scaling and addition), and affine space operations (vector-point addition and 
point-point-subtraction), with nice notations: + and <bu> for vector add and scaling,
and plus_sub_v and minus_sub_v for vector-point addition and point point substraction.

For clear, concise examples, see the file aff1Kcoord_std_test.lean.