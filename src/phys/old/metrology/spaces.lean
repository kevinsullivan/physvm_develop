/-
The dimensions.lean file implements the concept of physical dimensions
as we've understood it from, e.g., the SI system of dimensions and units.
Our insight is that that approach leaves too much structure behind. What
we do here, instead, it implement the concept of physical spaces. So, for
example, the vector space concept of (directed) lengths is replaced by the
affine space concept of a torsor of geometric points over a vector space 
of displacements. We will then define an algebra of *spaces* rather than
an algebra of dimensions, and that, I think, it really what we need in
order to implement a richly library of abstractions for doing strongly
and statically typed physics. --Sullivan Oct 20/2020

We need to distinguish between physical (e.g., geomtric) spaces and
labellings (coordinatizations) of points and vectors in these spaces. 
The reason we need to be careful is each labelling (defined by a frame)
gives us a new affine coordinate space, albeit one that is isomorphic
to any other such labelling.

Geometric space itself has an affine space structure, and so does each
labelling of this space. And we're going have to be careful here. If we
have two labellings of the same physical space, then we have to undestand 
that.#check

A coordinate-free abstraction erases all coordinatizations, and just
exposes abstractions of the underying points and vectors. The DeRose
library only considered coordinates when (1) instantiating a point in
relation to some affine frame, (2) asking for the coordinates of a point
with respect to a frame, and (3) in the hidden implementatoin when
applying affine transformations to map hidden coordinations between
different frames.

X, Y, and Z are real affine 1-spaces

X * Y * Z --- direct product of 3 one-spaces


N x R^2+ -> R+
-/

inductive space : Type
| geometry         -- real affine 1
| time              -- real affine 1
| mass              -- real quasi-affine monus 1 (negative mass speculative)
| temperature       -- real quasi-affine monus 1 (negative mass speculative)
| quantity          -- nat monus 1
-- intensity        -- 
-- current



def algebraOf : space → _  -- return algebraic structure for space

-- expect geometryOf geometry = affine 1 space 

/-
Operations on these spaces
-/

-- product of 1-d geometric spaces

def geometry2 := directProd space.geometry space.geometry   -- 2d geometry 

-- expect algebraOf geometry2 = 2-d affine space

-- algebraOf geometry/time := affine1d X affine1d
/-
Operations on spaces to produce new derived spaces where the underlying
albraic structures are correctly computed 
-/


/-
Once we've got the most basic spaces down,
all other spaces should be derived by applying
appropriate operators to the individual spaces,
for example, direct product.
-/

