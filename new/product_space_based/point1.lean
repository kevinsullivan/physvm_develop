import linear_algebra.affine_space.basic

/-
    n-DIMENSIONAL AFFINE K-COORDINATE TUPLE
    represented as (n+1)-dimensional tuple
-/

universes u --v w
variables 
{K : Type u} [ring K] [inhabited K] 
{α : Type u} [has_add α]

/-
Frameless points, vectors, frames
-/

def vec : Type u := { v : K × K // v.fst = (0:K) }
def mk_vec (k : K) : vec := ⟨(0,k), rfl⟩

def pt : Type u := { v : K × K // v.fst = (1:K) }
def mk_pt (k : K) : pt := ⟨(1,k), rfl⟩


def vec_zero := mk_vec (0:K)
def std_vec := mk_vec (1:K)

def std_pt : pt  := mk_pt (0:K)
def pt_zero : pt := mk_pt (0:K)


inductive fm : Type u
| base : fm
| deriv (self : prod (@pt K _ _) (@vec K _ _)) (parent : fm) : fm

def mk_fm (p : @pt K _ _) (v : @vec K _ _) (f : fm): fm := fm.deriv (p, v) f 

def std_fm : @fm K _ _ := fm.base  



/-
Framed points, vectors, frames
-/
structure spc (f : @fm K _ _) : Type u 

structure point {f : @fm K _ _} (s : @spc K _ _ f ) : Type u :=
(pt : @pt K _ _) 

structure vectr {f : @fm K _ _} (s : @spc K _ _ f ) : Type u :=
(vec : @vec K _ _) 

def mk_point {f : @fm K _ _} (s : @spc K _ _ f ) (k : K) : point s :=
point.mk (mk_pt k)  

def mk_vectr {f : @fm K _ _} (s : @spc K _ _ f ) (k : K) : vectr s :=
vectr.mk (mk_vec k)  

def mk_frame {parent : @fm K _ _} {s : @spc K _ _ parent}  (p : point s ) (v : vectr s) :=
  fm.deriv (p.pt, v.vec) parent

def mk_space (f : @fm K _ _) :=
  @spc.mk K _ _ f

/-
Std frameless 1-d space over K
Fix lack of type inference for
-/
def std_spc : spc (@std_fm K _ _) := mk_space std_fm

/-
Constants
-/


def std_point := mk_point std_spc (0:K) 
def std_vectr := mk_vectr std_spc (1:K)

-- Initial client-facing space instance
def std_frame : @fm K _ _ := mk_frame std_point std_vectr -- no infer K
def std_space := mk_space (@std_frame K _ _)              -- space for std_frame

