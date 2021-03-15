import .space_unframed

/-
Framed points, vectors, frames
-/

universes u --v w
variables 
{K : Type u} [ring K] [inhabited K] 

/-
The low-level spc type represents a space with a low-level frame
-/
structure spc (f : @fm K _ _) : Type u 

/-
On that we build client API types for points, vectors, frames, spaces
-/
-- Type of point, pt, in a space s coordinatized in terms of f
structure point {f : @fm K _ _} (s : @spc K _ _ f ) : Type u :=
(pt : @pt K _ _) 

-- Type of vectr, vc, in a space s coordinatized in terms of f
structure vectr {f : @fm K _ _} (s : @spc K _ _ f ) : Type u :=
(vec : @vec K _ _) 

-- Given point p and vector v in s, return a new frame f=(p,v) on s 
def mk_frame {parent : 
  @fm K _ _} {s : @spc K _ _ parent}  (p : point s ) (v : vectr s) :=
fm.deriv (p.pt, v.vec) parent   -- make sure v ≠ 0

def mk_point {f : @fm K _ _} (s : @spc K _ _ f ) (k : K) : point s :=
point.mk (mk_pt k)  

def mk_vectr {f : @fm K _ _} (s : @spc K _ _ f ) (k : K) : vectr s :=
vectr.mk (mk_vec k)  

def mk_space (f : @fm K _ _) :=
  @spc.mk K _ _ f

