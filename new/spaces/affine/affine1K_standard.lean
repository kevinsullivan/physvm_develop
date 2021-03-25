import .affine1K_framed

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
def std_fm : fm K    := fm.base  

/-
Build std_spc on this farme
-/
def std_spc : spc K (std_fm K) := mk_space K (std_fm K)

/-
Now we can build point and vectr objects in terms
of this space and any derived space and of related
frame (fm) objects. 
-/

/-
One values for points and vectrs 
-/
def point_zero := mk_point (std_spc K) 0
def vectr_one := mk_vectr (std_spc K) 1 
def std_frame := mk_frame (point_zero K) (vectr_one K) 
def std_space := mk_space K (std_frame K)

-- Exports: 

-- expose std_space, std_frame, point_zero, vectr_one