import .add_group_action
import .g_space tactic.ext
import algebra.module linear_algebra.basis

universes u v w
variables (X : Type u) (K : Type v) (V : Type w) (ι : Type*)
[field K] [add_comm_group V] [vector_space K V]


abbreviation affine_space
  (X K V : Type*)
  [field K] [add_comm_group V] [vector_space K V] := add_torsor V X

variables (s : finset ι) (g : ι → K) (v : ι → V) [is_basis K v] [affine_space X K V]

open_locale big_operators

def affine_combination (g_add : ∑ i in s, g i = 1) := ∑ i in s, g i • v i

def barycenter (g_add : ∑ i in s, g i = 1) := g -- TODO: want to coerce g to be a list?

structure affine_frame :=
(origin : X)
(vec : ι → V)
(basis : is_basis K vec)

section affine_with_frame

@[ext]
structure vec_with_frame (frame : affine_frame X K V ι) :=
(vec : V)

structure pt_with_frame (frame : affine_frame X K V ι) :=
(pt : X)

variables (basis : affine_frame X K V ι) (pt : X)

def vecf_add : vec_with_frame X K V ι basis → vec_with_frame X K V ι basis → vec_with_frame X K V ι basis :=
λ x y, ⟨x.1 + y.1⟩

def vecf_neg : vec_with_frame X K V ι basis → vec_with_frame X K V ι basis :=
λ x, ⟨-x.1⟩

def vecf_scalar : K → vec_with_frame X K V ι basis → vec_with_frame X K V ι basis :=
λ c x, ⟨c • x.1⟩

instance : has_add (vec_with_frame X K V ι basis) := ⟨vecf_add X K V ι basis⟩

instance : has_neg (vec_with_frame X K V ι basis) := ⟨vecf_neg X K V ι basis⟩

instance vec_has_zero : has_zero V := by refine add_monoid.to_has_zero V

def vecf_zero : vec_with_frame X K V ι basis := ⟨(vec_has_zero V).zero⟩

instance : has_zero (vec_with_frame X K V ι basis) := ⟨vecf_zero X K V ι basis⟩

instance : has_scalar K (vec_with_frame X K V ι basis) := ⟨vecf_scalar X K V ι basis⟩

#print add_comm_group

lemma vadd_assoc : ∀ x y z : vec_with_frame X K V ι basis, x + y + z = x + (y + z) := 
begin
intros,
cases x, cases y, cases z,
ext,
exact add_assoc x y z,
end

lemma vzero_add : ∀ x : vec_with_frame X K V ι basis, 0 + x = x :=
begin
intros,
cases x,
ext,
exact zero_add x,
end

lemma vadd_zero : ∀ x : vec_with_frame X K V ι basis, x + 0 = x :=
begin
intros,
cases x,
ext,
exact add_zero x,
end

lemma vadd_left_neg : ∀ x : vec_with_frame X K V ι basis, -x + x = 0 :=
begin
intros,
cases x,
ext,
exact add_left_neg x,
end

lemma vadd_comm : ∀ x y : vec_with_frame X K V ι basis, x + y = y + x := 
begin
intros,
cases x, cases y,
ext,
exact add_comm x y,
end

instance : add_comm_group (vec_with_frame X K V ι basis) :=
⟨
  vecf_add X K V ι basis, 
  vadd_assoc X K V ι basis, 
  vecf_zero X K V ι basis, 
  vzero_add X K V ι basis, 
  vadd_zero X K V ι basis, 
  vecf_neg X K V ι basis,
  vadd_left_neg X K V ι basis,
  vadd_comm X K V ι basis
⟩

#print vector_space
#print semimodule

instance : vector_space K (vec_with_frame X K V ι basis) := sorry

instance : affine_space (pt_with_frame X K V ι basis) K (vec_with_frame X K V ι basis) := sorry

end affine_with_frame