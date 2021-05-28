import .space_framed

universes u --v w
variables 
(K : Type u) [ring K] [inhabited K] 
{α : Type u} [has_add α]

/-
Standard space: 1-d affine with standard frame
-/

def std_fm : fm K    := fm.base  

def std_spc : spc K (@std_fm K _ _) := @mk_space K _ _ (std_fm K)

/-
One values for points and vectrs 
-/
def point_one := mk_point K (std_spc K) 1 
def vectr_one := mk_vectr K (std_spc K) 1 

/-
Zero values for points and vectrs 
-/
def point_zero := mk_point K (std_spc K) 0

/-
Standard point, vector, frame, space
-/
def std_point := mk_point K (std_spc K) 0 
def std_vectr := mk_vectr K (std_spc K) 1
def std_frame : fm K := mk_frame K (std_point K) (std_vectr K) 
def std_space := mk_space K (std_frame K)

-- Exports: 

-- expose std_space