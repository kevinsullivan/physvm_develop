import .space_framed

namespace standard

open framed

universes u --v w
variables 
(n : ℕ) (K : Type u) [ring K] [field K] [inhabited K] 
{α : Type u} [has_add α]

/-
Standard space: 1-d affine with standard frame
-/
def std_spc : unframed.space n K (unframed.std_frame n K) := mk_space (unframed.std_frame n K)

/-
One values for points and vectors 
-/
def point_one := mk_point (std_spc n K) (⟨list.repeat 1 n,begin
  simp [list.repeat],
end⟩ : vector K n) 
def vector_one := mk_vector (std_spc n K) (⟨list.repeat 1 n,begin
  simp [list.repeat],
end⟩ : vector K n)

/-
Zero values for points and vectors 
-/
def point_zero := mk_point (std_spc n K) (⟨list.repeat 0 n,begin
  simp [list.repeat],
end⟩ : vector K n)
def vector_zero := mk_vector (std_spc n K) (⟨list.repeat 0 n,begin
  simp [list.repeat],
end⟩ : vector K n) 

/-
Standard point, vector, frame, space
-/
def std_point := mk_point (std_spc n K) (⟨list.repeat 0 n,begin
  simp [list.repeat],
end⟩ : vector K n)
def std_basis := λi: fin n, mk_vector (std_spc n K) (⟨(list.repeat 0 n).update_nth i 1,begin
  simp [list.repeat],
end⟩ : vector K n)
def std_frame : unframed.frame n K := mk_der_frame (std_point n K) (std_basis n K)
def std_space := mk_space (std_frame n K)

-- Exports: 

-- expose std_space

end standard