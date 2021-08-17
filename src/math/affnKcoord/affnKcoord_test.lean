import .affnKcoord_transforms

/-
Let K represent the field of rational numbers.
-/
abbreviation K := ℚ 

/-
Let the dimension of our space be three.
-/
def dim := 3

/-
We assign a unique natural number identifier, 
first_id = 1, to our space to distinguish it from
other possible spaces of the same dimension over 
the same field. 
-/
def first_id := 1

/-
Let std_fm be a standard affine frame of dimension,
dim, on a space with unique identifier, first_id.
-/
def std_fm : fm K dim first_id := fm.base dim first_id

/-
Let std_sp be an *affine coordinate space* in which
coordinates are interpreted with respect to std_fm.
-/
def std_sp := mk_space std_fm

/-
Note that first_id, the space identifier, is lifted 
to an indexed sequence of space identifiers, in this
case with just one entry.
-/
#check std_fm


/-
Let p1 be a point with coordinates [1,2,3] in std_sp,
our affine coordinate 3-space with the standard frame,
std_fm. 

API for making points:

- K, implicit, is a non-empty field
- dim, implicit, is the affine space dimension 
- id_vec, implicit, is a sequence of space identifiers
- f, implicit, is a frame on the product space
- s is the affine coordinate system defined by f
- (vector K dim) is a dim-length list of coordinates in K

Given these arguments, this function returns a point,
in the *affine coordinate space*, s.

mk_point : Π 
  {K : Type u} [_inst_1 : field K] [_inst_2 : inhabited K] 
  {dim : ℕ} 
  {id_vec : fin dim → ℕ} 
  {f : fm K dim id_vec} 
  (s : spc K f), 
  vector K dim → point s
-/
def p1 : point std_sp := 
  mk_point std_sp (⟨[1,2,3], rfl⟩ : vector K 3)

def p1c : fin dim → pt K := p1.coords

-- KEVIN: QUESTIONS HERE
#check p1
#check p1.coords
#check p1c

/-
Let v1 be a vector with coordinates [2,5,8] with respect
to the standard frame in our std_sp.
-/
def v1 : vectr std_sp :=
  mk_vectr _ ⟨[2,5,8], rfl⟩

/-
We can now write type-checked affine space
operations involving such points and vectors.
Type checking ensures that points and vectors
are from the same affine coordinate space (ACS). 
-/

/-
Let p2 be p1 translated by thrice by v1.
-/
def p2 := 3•v1 +ᵥ p1

/-
Adding point to point is undefined. 
-/
def bad_point_add := p2 +ᵥ p2 

/-
Point minus point yields vector (in the same ACS)
-/
def v2 := p2 -ᵥ p1

/-
More examples.
-/
def v3 := (1/4 : ℚ)•v2 +ᵥ (mk_vectr std_sp ⟨[-1,0,1], rfl⟩)

/-
Scalar multiplication
-/
#eval (1/4:K)•(4:K)

def vecd : vec K := (1/4 : K)•(mk_vec K 6)
#eval vecd

/-
Let der_fm1 be a frame "derived" from the std_fm
with origin p2 and basis comprising [v1, v2, v3].

KEVIN: Need a helper function that takes a list
(Lean "vector") of length n of coordinates (like 
v1.coords) and that returns indexed sequence for
use by the fm.deriv (derived frame) constructor.
Use Lean matrix here?
-/
def der_fm1 : fm K dim first_id := fm.deriv 
  p2.coords 
  (λi, match i.1 with
    | 0 := v1.coords
    | 1 := v2.coords
    | _ := v3.coords
    end)
  sorry sorry std_fm

/-
Define my_pt and vectors u4-u6 in std_sp as arguments
to create a derived frame, myder and space, myderspc.
-/
def my_pt : point std_sp := mk_point std_sp ⟨[1,1,1],rfl⟩
def u4 : vectr std_sp := mk_vectr std_sp ⟨[6,0,0],rfl⟩
def u5 : vectr std_sp := mk_vectr std_sp ⟨[0,6,0],rfl⟩
def u6 : vectr std_sp := mk_vectr std_sp ⟨[0,0,6],rfl⟩

def myder : fm K dim first_id
    := fm.deriv my_pt.coords (λi, match i.1 with
    | 0 := u4.coords
    | 1 := u5.coords
    | _ := u6.coords
    end) sorry sorry std_sp.fm 

def mydersp := mk_space myder

/-
Let pt2 by a point with coordinates [1,1,1] in
the affine coordinate space, mydersp.
-/
def pt2 := mk_point mydersp ⟨[1,1,1],rfl⟩

/-
Let tf be an affine transformation taking points
and vectors in mydersp to corresponding points and
vectors in std_sp.

spc.fm_tr : Π 
  {K : Type} [_inst_1 : field K] [_inst_2 : inhabited K] 
  {dim : ℕ} 
  {id_vec : fin dim → ℕ} {f1 f2 : fm K dim id_vec} 
  (s1 : spc K f1) 
  (s2 : spc K f2), 
  fm_tr s1 s2
-/
def tf := mydersp.fm_tr std_sp

#check tf

def tfd : point std_sp := tf.transform_point pt2

/-
KEVIN: Let's discuss.
-/
#eval tfd.coords ⟨2, sorry⟩


/-
From a frame, myder, get (Lean) matrix of homogeneous coordinates
-/
def homder := myder.to_homogeneous_matrix

/-
WARNING : ALL MATRIX EVALUATION BROKEN AS OF 6/17 DUE TO INTRODUCTION OF 
LINEAR INDEPENDENCE AND SPANNING PROOFS IN FM.DERIV DEFINITION

THIS MUST BE SOLVED OR REMOVED IN ORDER TO EVALUATE TRANSFORM RESULTS OR 
COORDINATES OF MATRICES.
-/


#check v1.coords
#eval p2.coords ⟨3,sorry⟩
#eval v1.coords ⟨2,sorry⟩
#eval v2.coords ⟨2,sorry⟩
#eval v3.coords ⟨0,sorry⟩
#eval homder 2 3

#eval homder ⟨0,sorry⟩ ⟨0,sorry⟩
#eval homder 1 0
#eval homder 2 0
#eval homder 3 0
#eval homder 0 1
#eval homder 1 1
#eval homder 2 1
#eval homder 3 1
#eval homder 0 2
#eval homder 1 2
#eval homder 2 2
#eval homder 3 2
#eval homder 0 3
#eval homder 1 3
#eval homder 2 3
#eval homder 3 3

/-
Given matrix of homogeneous coordinates for transform
obtained from a frame (therefore invertible) compute the
matrix of the homogeneous coordinates of inverse matrix.
-/
def homder_inv := homder.cramer_inverse

#check homder_inv

/-
Confirm that these matrices contained the expected values.
-/
#eval homder_inv ⟨0,sorry⟩ ⟨0,sorry⟩
#eval homder_inv 1 0
#eval homder_inv 2 0
#eval homder_inv 3 0
#eval homder_inv 0 1
#eval homder_inv 1 1
#eval homder_inv 2 1
#eval homder_inv 3 1
#eval homder_inv 0 2
#eval homder_inv 1 2
#eval homder_inv 2 2
#eval homder_inv 3 2
#eval homder_inv 0 3
#eval homder_inv 1 3
#eval homder_inv 2 3
#eval homder_inv 3 3

def inv_mul := homder_inv.mul homder

#check inv_mul
#eval inv_mul ⟨0,sorry⟩ ⟨0,sorry⟩
#eval inv_mul 1 0
#eval inv_mul 2 0
#eval inv_mul 3 0
#eval inv_mul 0 1
#eval inv_mul 1 1
#eval inv_mul 2 1
#eval inv_mul 3 1
#eval inv_mul 0 2
#eval inv_mul 1 2
#eval inv_mul 2 2
#eval inv_mul 3 2
#eval inv_mul 0 3
#eval inv_mul 1 3
#eval inv_mul 2 3
#eval inv_mul 3 3

#eval homder 0 0




/-
Show that we can obtain transforms between
arbitrary affine coordinate spaces.
-/

def der_sp1 : spc K der_fm1 := mk_space der_fm1

def der_fm2 : fm K dim first_id := fm.deriv 
  p2.coords 
  (λi, match i.1 with
    | 0 := v2.coords
    | 1 := v3.coords
    | _ := v1.coords
    end)
  sorry sorry std_fm

def der_sp2 : spc K der_fm2 := mk_space der_fm2

def der_vec1 : vectr der_sp1 := mk_vectr _ ⟨[1,2,3],rfl⟩

def der_vec2 : vectr der_sp2 := mk_vectr _ ⟨[1,2,3],rfl⟩

def bad_sp_add := der_vec1 +ᵥ der_vec2

def der1_to_2 := der_sp1.fm_tr der_sp2

def trans_der_vec1 : vectr der_sp2 := der1_to_2.transform_vectr der_vec1

def okay_sp_add : _ := (der1_to_2.transform_vectr der_vec1) +ᵥ der_vec2

/-
KEVIN: Questions about this.
-/
#check (der_vec1.expressed_in der_sp2)


