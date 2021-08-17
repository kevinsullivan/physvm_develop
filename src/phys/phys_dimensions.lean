/-
Our design supports a set of disjoint 1-D affine spaces
indexed by natural numbers, each with a standard frame,
in terms of which new affine coordinate space "overlays"
can be constructed. 

Our model here in the phys layer is that each physical
dimension has its own coordinate-free, disjoint affine
space. Currently, time and length are the only two we
really support. We're speculating that perhaps mass is
in the list as well? (Yet, its algebra isn't affine.)
-/

/-
Indices to disjoint 1-D "standard" affine spaces, and
thus modeling distinct affine spaces of the physical
world (construed classically).
-/
def TIME := 0
def LENGTH := 1
