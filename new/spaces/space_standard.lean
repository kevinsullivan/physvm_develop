import .space_framed

universes u --v w
variables 
{K : Type u} [ring K] [inhabited K] 
{α : Type u} [has_add α]

/-
Standard space: 1-d affine with standard frame
-/
def std_spc : spc (@std_fm K _ _) := mk_space std_fm

/-
One values for points and vectrs 
-/
def point_one := mk_point std_spc (1:K) 
def vectr_one := mk_vectr std_spc (1:K) 

/-
Zero values for points and vectrs 
-/
def point_zero := mk_point std_spc (0:K) 
def vectr_zero := mk_vectr std_spc (0:K) 

/-
Standard point, vector, frame, space
-/
def std_point := mk_point std_spc (0:K) 
def std_vectr := mk_vectr std_spc (1:K)
def std_frame : @fm K _ _ := mk_frame std_point std_vectr 
def std_space := mk_space (@std_frame K _ _)

-- Exports: 

-- expose std_space