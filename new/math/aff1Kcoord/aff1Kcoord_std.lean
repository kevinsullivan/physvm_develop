import .aff1Kcoord

universes u 
variables 
(K : Type u) [field K] [inhabited K] 
{α : Type u} [has_add α]

/-
Standard K affine 1-space
-/

/-
Represent standard frame with fm.base
-/
def std_fm (n : nat) : fm K n   := fm.base n

/-
Build std_spc on this farme
-/
def std_spc (n : nat) : spc K (std_fm K n) := mk_space K (std_fm K n) 

/-
Now we can build point and vectr objects in terms
of this space and any derived space and of related
frame (fm) objects. 
-/

/-
Basic values for points and vectrs 
-/
def point_zero (n : nat) := mk_point (std_spc K n) 0
def vectr_one  (n : nat) := mk_vectr (std_spc K n) 1 
def std_frame  (n : nat) := mk_frame (point_zero K n) (vectr_one K n) 
def std_space  (n : nat) := mk_space K (std_frame K n) 

-- Exports: 

-- expose std_space, std_frame, point_zero, vectr_one