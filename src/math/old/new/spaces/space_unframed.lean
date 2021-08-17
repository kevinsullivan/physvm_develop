import linear_algebra.affine_space.basic
import algebra.direct_sum

namespace unframed

universes u --v w

variables 
(n : ℕ) (K : Type u) [ring K] [field K] [inhabited K] 

open_locale big_operators
#check direct_sum 

/-
Frameless points, vectors, frames
-/
def vec : Type u := (fin n) → K --{ v : K × K // v.fst = (0:K) }
def mk_vec (k : vector K n) : vec n K := λi, k.nth i

def pt : Type u := (fin n) → K--{ v : K × K // v.fst = (1:K) }
def mk_pt (k : vector K n) : pt n K := λi, k.nth i

inductive frame : Type u
| base : frame-- what is the standard frame then...?
| deriv (self : prod (pt n K) (fin n → vec n K)) (parent : frame) : frame
def mk_derived (p : pt n K) (b : fin n → vec n K) (f : frame n K): frame n K := frame.deriv (p, b) f 
/-
def mk_frame 
{parent : frame K } {s : space parent}  
(p : point s ) (v : vector s) : frame K :=
frame.deriv (p.pt, v.vec) parent   -- make sure v ≠ 0


-/
/-
One values for pts and vecs 
-/
def pt_one : pt n K := mk_pt n K (⟨list.repeat 1 n,begin
  simp [list.repeat],
end⟩ : vector K n)
def vec_one : vec n K := mk_vec n K (⟨list.repeat 1 n,begin
  simp [list.repeat],
end⟩ : vector K n)

/-
Zero values for pts and vecs
-/
def pt_zero : pt n K := mk_pt n K (⟨list.repeat 0 n,begin
  simp [list.repeat],
end⟩ : vector K n)
def vec_zero : vec n K := mk_vec n K (⟨list.repeat 0 n,begin
  simp [list.repeat],
end⟩ : vector K n)

/-
std pt, vec, frame
-/
--def std_vec : vec n K  := vec_one n K 
--def std_pt : pt n K    := pt_zero n K
--def std_frame : frame n K    := frame.base  
def std_frame : frame n K := frame.base
def std_pt := pt_zero n K
def std_vec (i : fin n) := mk_vec n K  (⟨(list.repeat 0 n).update_nth i 1,begin
  simp [list.repeat],
end⟩ : vector K n)
def std_basis : fin n → vec n K :=
  λi, std_vec n K i
  


def frame.origin 
  {n : ℕ}
  {K : Type*}
  [field K]
  [inhabited K]
  (f : frame n K) : pt n K :=
  begin
    cases f,
    { exact pt_zero n K },
    { exact f_self.1 }
  end

def frame.basis 
  {n : ℕ}
  {K : Type*}
  [field K]
  [inhabited K]
  (f : frame n K) : fin n → vec n K :=
  begin
    cases f,
    { exact std_basis n K },
    { exact f_self.2 }
  end

/-
The low-level space type represents a space with a low-level frame
-/
structure space (f : frame n K) := 
mk::
  --(x1 : direct_sum (fin n) f.basis)

--structure product_space (f : frame n K) : 


variables (v1 v2 v3 : vec n K)

#check v1 ⨁ v2

end unframed