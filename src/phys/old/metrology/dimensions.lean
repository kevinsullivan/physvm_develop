import data.real.basic

/-

The abstraction implemented in this component supports SI-like
physical dimensions and measurement systems, including SI and 
Imperial. Kevin believe it's not quite right, insofar as the 
SI system isn't based on the right abstractions. For example, 
it enables the expression of displacements but not positions. 
In other words, it's oriented to explicit representations of 
vector but not point physical quantities.

A physical dimesion is a space of physical objects (quantities)
independent of a specific measurement system / coordinate frame.
Basic physical dimensions include time and geometric space.
Derived dimensions are obtained by inverting and multiplying
basic dimensions. So, for example, velocity is obtained by 
multiplying geometric space by the inverse of time. 

A key to understanding our design is to see that we define two
types: BasicDimension and Dimension. BasicDimension represents
the set of basic dimension of the SI system only, while Dimension
represents the set of basic and derived dimensions. The function
basicDimToDim returns a Dimension value for each BasicDimension
value, injecting the set of basic dimensions into the set of 
basic and derived dimensions.  
-/ 



/-
First we enumerate the basic dimensions of the SI system.
-/

namespace dimension

-- Basic dimensions of the SI system 
inductive BasicDimension : Type
| length
| mass 
| time
| current
| temperature
| quantity
| intensity

/-
Next we associate a scalar type with each basic dimension.
These scalars will express amounts in a given dimension. 
-/

def basicDimScalarType : BasicDimension → Type 
| BasicDimension.length := ℝ    -- space infinitely divisible (not true)
| BasicDimension.time := ℝ      -- time infinitely divisible (not true)
| BasicDimension.mass := { r : ℝ // r >= 0} -- mass can't be negative
| BasicDimension.current := ℝ   -- currents can be negative or positive
| BasicDimension.temperature := { r : ℝ // r >= 0 } -- ∃ absolute zero
| BasicDimension.quantity := ℕ  -- quantity is a count of particles
| BasicDimension.intensity := {r : ℝ // r >= 0}    -- is this right?

/-
Now we represent an arbitrary derived dimension as a 7-tuple of 
rational exponents corresponding to the basic dimensions. It's
well known that the algebraic structure of this set is that of 
an additive commutative (abelian) group. (Should be proved.)
For example, the dimension for velocity is <1,0,-1, 0, 0, 0, 0>.
ToDo: Is ℚ really the right type for these values? Do we need
fractional dimensions?
-/
structure Dimension  : Type :=
mk :: 
(length: ℚ)
(mass : ℚ)
(time : ℚ)
(current: ℚ)
(temperature : ℚ)
(quantity : ℚ)
(intensity: ℚ)

/-
Here is the injection of BasicDimension into Dimension.
-/
def basicDimToDim : BasicDimension → Dimension
| BasicDimension.length := Dimension.mk 1 0 0 0 0 0 0
| BasicDimension.mass := Dimension.mk 0 1 0 0 0 0 0
| BasicDimension.time := Dimension.mk 0 0 1 0 0 0 0
| BasicDimension.current := Dimension.mk 0 0 0 1 0 0 0
| BasicDimension.temperature := Dimension.mk 0 0 0 0 1 0 0
| BasicDimension.quantity := Dimension.mk 0 0 0 0 0 1 0
| BasicDimension.intensity := Dimension.mk 0 0 0 0 0 0 1

/-
Here now are  functions for computing derived dimensions. 
-/
-- Functions that compute derived dimensions
def mul : Dimension → Dimension → Dimension 
| (Dimension.mk l m t c p q i) (Dimension.mk l' m' t' c' p' q' i') := 
  Dimension.mk (l+l') (m+m') (t+t') (c+c') (p+p') (q+q') (i+i')

instance : has_mul Dimension := ⟨mul⟩

def inv : Dimension → Dimension 
| (Dimension.mk l m t c p q i) := (Dimension.mk (-l) (-m) (-t) (-c) (-p) (-q) (-i) ) 

def div : Dimension → Dimension → Dimension 
| q1 q2 := mul q1 (inv q2)

/-
Standard claim: the set of dimensions forms a multiplicative
abelian (commutative) group. But is this really true? If, for
example, quantity of material is measured as a natural number,
what quantity do you get when you take 1/2 of 3 particles? If
the notion is that particles are indivisible then this either
makes no sense, or the answer is 1 remainder 1, and what does
that mean? For now, we state the usual claim, but we think it
requires more thought.
-/
instance dimensionIsAbelianGroup : add_comm_group Dimension := sorry


-- tell me the algebraic structure of give basic dimension

/-
def algebraOf : BasicDimension → Type
| BasicDimension.length := ℝ --real_affine.Algebra--affine_space (aff_pt_coord_tuple ℝ 1) ℝ (aff_vec_coord_tuple ℝ 1)
| BasicDimension.mass := { m : ℝ // m >= 0}
| BasicDimension.time := ℝ--affine_space (aff_pt_coord_tuple ℝ 1) ℝ (aff_vec_coord_tuple ℝ 1)
| BasicDimension.current := ℝ 
| BasicDimension.temperature := { m : ℝ // m >= 0} -- exists absolute zero
| BasicDimension.quantity := ℕ 
| BasicDimension.intensity := { m : ℝ // m >= 0}
-/

/-
def algebraOfDimension : Dimension → real_affine.Algebra
| (Dimension.mk l m t c p q i) := real_affine.Algebra.aff_space (real_affine.to_affine 1)
-/

end dimension
