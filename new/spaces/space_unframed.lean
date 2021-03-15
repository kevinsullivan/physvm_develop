import linear_algebra.affine_space.basic

universes u --v w

variables 
{K : Type u} [ring K] [inhabited K] 

/-
Frameless points, vectors, frames
-/
def vec : Type u := { v : K × K // v.fst = (0:K) }
def mk_vec (k : K) : vec := ⟨(0,k), rfl⟩

def pt : Type u := { v : K × K // v.fst = (1:K) }
def mk_pt (k : K) : pt := ⟨(1,k), rfl⟩

inductive fm : Type u
| base : fm
| deriv (self : prod (@pt K _ _) (@vec K _ _)) (parent : fm) : fm
def mk_fm (p : @pt K _ _) (v : @vec K _ _) (f : fm): fm := fm.deriv (p, v) f 

/-
One values for pts and vecs 
-/
def pt_one : pt := mk_pt (1:K)
def vec_one := mk_vec (1:K)

/-
Zero values for pts and vecs
-/
def pt_zero : pt := mk_pt (0:K)
def vec_zero := mk_vec (0:K)

/-
std pt, vec, fm
-/
def std_vec : @vec K _ _  := vec_one 
def std_pt : @pt K _ _    := pt_zero 
def std_fm : @fm K _ _    := fm.base  



