import .affnKcoord_transforms

universes u 
variables 
(K : Type u) [field K] [inhabited K] 
{α : Type u} [has_add α] (space_id : ℕ) (dim : ℕ)

/-
Standard K affine 1-space
-/

/-
Represent standard frame with fm.base
-/
def std_fm : fm K space_id dim   := fm.base space_id dim

/-
Build std_spc on this farme
-/
def std_spc : spc K (std_fm K dim space_id) := mk_space (std_fm K dim space_id) 

/-
Now we can build point and vectr objects in terms
of this space and any derived space and of related
frame (fm) objects. 
-/

/-
Basic values for points and vectrs 
-/
def point_zero := mk_point (std_spc K dim space_id) ⟨list.repeat 0 dim, sorry⟩
def vectr_one  := mk_vectr (std_spc K dim space_id) ⟨list.repeat 1 dim, sorry⟩ 
def std_frame  := mk_frame (point_zero K dim space_id) (λi, vectr_one K dim space_id) 
def std_space  := mk_space (std_frame K dim space_id) 

-- Exports: 

-- expose std_space, std_frame, point_zero, vectr_one