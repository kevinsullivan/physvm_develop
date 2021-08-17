# Overview of affnKcoord folder

## affnK.lean
There is a short, simple file called "affnK.lean" which describes multidimensional "unframed" points and vectors, which are just indexed sets of pt's and vec's (unframed). 

## affnKcoord_definitions.lean
Next, there is a file called "affnKcoord_definitions.lean", which is essentially the beginning of 4 files (which are essentially 1 file broken into 4 sequential files) where the proofs begin. This file describes affine frames, affine spaces, and built on top of those are framed points and vectors (vectrs). Most of the proofs in here are simple, except for the basis proofs (linear independence and spanning the image) which, although they look feasible, require a lot of knowledge of Lean machinery. 

## affnKcoord_vectorspace.lean
The following file, which  "affnKcoord_definitions.lean" is antecedent to, is "affnKcoord_vectorspace.lean". This is essentially a set of lemmas and type class instances which ultimately prove that vectrs (framed vectors) form a module over the field which their individual coordinates are composed of (which is also a vector space). The lemmas are mostly straightforward. They're mostly of the form of something like vectr addition is commutative, or 0 vectr + any other vectr = any other vectr.

## affnKcoord_affinespace.lean
The penultimate file is "affnKcoord_affinespace.lean". This file is a bit shorter, and ultimately leads to a proof that points and vectrs form an affine space. It contains some definitions such as interactions between/operations on points and vectrs, as well as a few type class instances and lemmas.

## affnKcoord_transforms.lean
The final file is "affnKcoord_transforms.lean". This is the longest file. It contains helper methods used in the construction of affine transforms, such as turning frames into a homogeneous matrix (a lean/mathlib matrix), points and vectrs into homogeneous vectrs/points expressed in mathlib style (fin nat \to K, where K is a field here). There is a definition of a matrix inverse there using Cramer's rule which we need to use as Lean's definition is noncomputable. Next, there are several procedures which define how affine transforms are constructed. 

Affine transforms are simply a mathematical object, which can be represented as a homogeneous matrix or an affine function, which allow you to convert a point or vectr expressed in one frame into another frame. These frames all derive from a standard frame (eye matrix + 0 origin), and so they form what you can think of as a "tree". The affine transform functions is thus essentially a "tree search" to find the transform between any two arbitrary frames in the tree. 

