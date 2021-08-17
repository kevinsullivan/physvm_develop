import .space_unframed
import linear_algebra.affine_space.basic

/-
Framed points, vectors, frames
-/
namespace framed

open_locale affine
open unframed

universes u --v w
variables 
{n : ℕ } {K : Type u} [ring K] [field K] [inhabited K] 

/-
On that we build client API types for points, vectors, frames, spaces
-/
-- Type of point, pt, in a space s coordinatized in terms of f
structure framed_point {f : frame n K} (s : space n K f ) : Type u :=
(pt : pt n K) 

-- Type of vector, vc, in a space s coordinatized in terms of f
structure framed_vector {f : frame n K } (s : space n K f ) : Type u :=
(vec : vec n K) 

instance ac {f : frame n K } {s : space n K f } : add_comm_group (framed_vector s) := sorry
instance aff {f : frame n K } {s : space n K f } : affine_space (framed_vector s) (framed_point s) := sorry

#check mk_frame

-- Given point p and vector v in s, return a new frame f=(p,v) on s 
def mk_der_frame 
{parent : frame n K } {s : space n K parent}  
(p : framed_point s) (v : fin n → framed_vector s) : frame n K :=
frame.deriv (p.pt, λi, (v i).vec) parent   -- make sure v ≠ 0

def mk_point {f : frame n K } (s : space n K f ) (k : vector K n) : framed_point s :=
⟨(mk_pt n K k)⟩

def mk_vector {f : frame n K } (s : space n K f ) (k : vector K n) : framed_vector s :=
⟨(mk_vec n K k)⟩

def mk_space (f : unframed.frame n K ) : space n K f:=
  space.mk 


--can't write these functions at unframed level with derived frames
def frame.origin 
   {f : frame n K } {s : space n K f } : framed_point s :=
  begin
    cases f,
    { exact ⟨pt_zero n K⟩ },
    { exact ⟨f_self.1⟩ }
  end

def frame.basis 
  {f : frame n K } {s : space n K f } : fin n → framed_vector s :=
  begin
    cases f,
    { exact (λi, ⟨unframed.std_basis n K i⟩)  },
    { exact (λi, ⟨f_self.2 i⟩) }
  end


end framed