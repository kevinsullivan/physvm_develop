import .space_standard

universes u 
variables 
{K : Type u} [ring K] [inhabited K] 
{α : Type u} [has_add α]

/-
CONSTRUCTING STANDARD SPACE.
1. We're given std_spc from library
2. Build a frame, f, on/in std_spc
3. Instantiate std_space around f 
-/

def point_std := mk_point std_spc (2:K) 
def vectr_std := mk_vectr std_spc (10:K)
def frame_std : @fm K _ _ := mk_frame point_std vectr_std  -- no infer K
def space_new := mk_space (@frame_std K _ _)              -- space for newFrame

#check @point_std 
#reduce @point_std 
#check point_std.pt.val.fst
#check point_std.pt.val.snd
#reduce point_std.pt.val.fst
#reduce point_std.pt.val.snd
#check @vectr_std 
#reduce @vectr_std 
#check vectr_std.vec.val.fst
#check vectr_std.vec.val.snd
#reduce vectr_std.vec.val.fst
#reduce vectr_std.vec.val.snd

/-
CONSTRUCTING A DERIVED "SPACE_X"
1. Build frame, f, on parent space
2. Instantiate new space on frame, f 
-/

def point_new := mk_point space_new (3:K)
def vectr_new := mk_vectr space_new (2:K)
def frame_new : @fm K _ _ := mk_frame point_new vectr_new
def space_x := mk_space (@frame_new K _ _) 

/-
That demonstrates space trees. But what we need
are product space types.
-/

def framed_space := (Σ f : (@fm K _ _), (@spc K _ _ f ))

-- WEAK TYPING HERE -- YIKES -- HMM
def frmd_std : @framed_space K _ _ := ⟨ frame_std, space_new ⟩ 
def frmd_new : @framed_space K _ _ := ⟨ frame_new, space_x ⟩ 

-- My really cool new space is a product space of space_x and space_x
