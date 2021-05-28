# 1 K Affine Space

To use this library, import aff1Kcoord_std. This module provides an abstraction of 1-D affine K coordinate spaces, rooted at a std_space, with points and vectors respectively each having their single (1-D) coordinates from an arbitrary field, K.

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

## Revision

We can't have common base affine spaces for different physical dimensions. In the commit, kevin, active at this writing, we've extended fm with nat ids as type elements, but in retrospect it now appears worth evaluating attaching ids to spaces instead. 

Spaces with unique physical dimension ids can serve as roots for coordinatizations via their base affine frames. Points and vectors belong to such spaces and are identified by coordinates relative to their base frame. New frames can be formed, and new coordinate system spaces instantiated. 

Will label this commit with the tag fm-id-version, then move ids from fm to spc. (Done.)