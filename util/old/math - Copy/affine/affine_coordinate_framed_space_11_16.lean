import .list_as_k_tuple linear_algebra.affine_space.basic
import linear_algebra.basis
import .affine_coordinate_space
import data.real.basic



open list
open vecl

namespace aff_fr

universes u v w

variables 
    -- (id : ℕ)
    (X : Type u) 
    (K : Type v) 
    (V : Type w) 
    (n : ℕ) 
    (k : K)
    (ι : Type*)
    (s : finset ι) 
    (g : ι → K) 
    (v : ι → V) 
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    [is_basis K v] 
    [affine_space V X]

/-
An affine frame comprises an origin point
and a basis for the vector space.
-/
structure affine_tuple_coordinate_frame
(K : Type w)
(n : ℕ)
[inhabited K]
[field K]  :=
mk ::
    (origin : aff_pt_coord_tuple K n) 
    (basis : (fin n) → aff_vec_coord_tuple K n) 
    (proof_is_basis : is_basis K basis) 

structure affine_derived_coordinate_frame extends 
    affine_tuple_coordinate_frame K n :=
mk ::
    (base : affine_tuple_coordinate_frame K n)

instance: has_lift (affine_derived_coordinate_frame K n) (affine_tuple_coordinate_frame K n) := ⟨sorry⟩

/-
inductive affine_coordinate_frame 
(K : Type w)
(n : ℕ)
[inhabited K]
[field K] : affine_tuple_coordinate_frame K n → Type
| standard 
: affine_coordinate_frame
--(origin : X) 
--(basis : (fin n) → aff_vec_coord_tuple K n) 
--(proof_is_basis : is_basis K basis) : affine_coordinate_frame
| derived 
    (origin : aff_pt_coord_tuple K n) 
    (basis : (fin n) → aff_vec_coord_tuple K n) 
    (proof_is_basis : is_basis K basis) 
    (fr : affine_coordinate_frame)
    : affine_coordinate_frame
-/
/-
mutual inductive affine_coordinate_frame, aff_coord_pt, aff_coord_vec
with affine_coordinate_frame : Type
| std_frame 
| gen_frame 
    (origin : aff_coord_pt) 
    (basis : ι → aff_coord_vec) 
    (proof_is_basis : is_basis K basis)
with aff_coord_pt : affine_coordinate_frame X K V ι →  Type
| mk (tuple : aff_pt_coord_tuple K n)
with aff_coord_vec : affine_coordinate_frame X K V ι → Type
| mk (tuple : aff_vec_coord_tuple K n)
-/

structure aff_coord_pt (fr : affine_tuple_coordinate_frame K n) 
            extends aff_pt_coord_tuple K n :=
   -- (tuple : aff_pt_coord_tuple K n)
   mk ::

structure aff_coord_vec (fr : affine_tuple_coordinate_frame K n) 
            extends aff_vec_coord_tuple K n  :=
   -- (tuple : aff_vec_coord_tuple K n)
   mk ::
/-
def affine_coordinate_frame_origin (frame : affine_coordinate_frame X K V ι) :=
match frame with
| std_frame := _
| gen_frame o b pf := o
end

def frame_basis : affine_frame X K V ι → (ι → V) :=
| (affine_frame.std_frame origin) := basis
| (affine_frame.gen_frame origin _ _) := origin
-/


variables 
    (fr : affine_tuple_coordinate_frame K n) 
    (cv1 cv2 : aff_coord_vec K n fr) 
    (cp1 cp2 : aff_coord_pt  K n fr)

/-
-- lemmas so that the following operations are well-defined
/-- the length of the sum of two length n+1 vectors is n+1 -/
lemma aff_not_nil : x.1 ≠ [] := 
begin
intro h,
have f : 0 ≠ n + 1 := ne.symm (nat.succ_ne_zero n),
have len_x_nil : length x.1 = length nil := by rw h,
have len_fixed : length nil = n + 1 := eq.trans (eq.symm len_x_nil) x.2,
have bad : 0 = n + 1 := eq.trans (eq.symm len_nil) len_fixed,
contradiction,
end

lemma aff_cons : ∃ x_hd : K, ∃ x_tl : list K, x.1 = x_hd :: x_tl :=
begin
cases x,
cases x_l,
{
    have f : 0 ≠ n + 1 := ne.symm (nat.succ_ne_zero n),
    have bad := eq.trans (eq.symm len_nil) x_len_fixed,
    contradiction
},
{
    apply exists.intro x_l_hd,
    apply exists.intro x_l_tl,
    exact rfl
}
end

/-- head is compatible with addition -/
lemma head_sum : head x.1 + head y.1 = head (ladd x.1 y.1) := 
begin
cases x,
cases y,
cases x_l,
    have f : 0 ≠ n + 1 := ne.symm (nat.succ_ne_zero n),
    have bad := eq.trans (eq.symm len_nil) x_len_fixed,
    contradiction,
cases y_l,
    have f : 0 ≠ n + 1 := ne.symm (nat.succ_ne_zero n),
    have bad := eq.trans (eq.symm len_nil) y_len_fixed,
    contradiction,
have head_xh : head (x_l_hd :: x_l_tl) = x_l_hd := rfl,
have head_yh : head (y_l_hd :: y_l_tl) = y_l_hd := rfl,
rw head_xh at x_fst_zero,
rw head_yh at y_fst_zero,
simp [x_fst_zero, y_fst_zero, add_cons_cons 0 0 x_l_tl y_l_tl],
end

/-- the head of the sum of two vectors is 0 -/
lemma sum_fst_fixed : head (ladd x.1 y.1) = 0 :=
    by simp only [eq.symm (head_sum K n x y), x.3, y.3]; exact add_zero 0

/-- the length of the zero vector is n+1 -/
lemma len_zero : length (zero_vector K n) = n + 1 :=
begin
induction n with n',
refl,
{
have h₃ : nat.succ (n' + 1) = nat.succ n' + 1 := rfl,
have h₄ : length (zero_vector K (nat.succ n')) = nat.succ (n' + 1) :=
    by {rw eq.symm n_ih, refl},
rw eq.symm h₃,
exact h₄,
}
end

/-- the head of the zero vector is zero -/
lemma head_zero : head (zero_vector K n) = 0 := by {cases n, refl, refl}

lemma vec_len_neg : length (vecl_neg x.1) = n + 1 := by {simp only [len_neg], exact x.2}

lemma head_neg_0 : head (vecl_neg x.1) = 0 :=
begin
cases x,
cases x_l,
contradiction,
rw neg_cons x_l_hd x_l_tl,
have head_xh : head (x_l_hd :: x_l_tl) = x_l_hd := rfl,
have head_0 : head (0 :: vecl_neg x_l_tl) = 0 := rfl,
rw head_xh at x_fst_zero,
simp only [x_fst_zero, neg_zero, head_0],
end

-/
def vec_add_coord : aff_coord_vec K n fr → aff_coord_vec K n fr → aff_coord_vec K n fr :=
    λ x y, ⟨⟨ladd x.1.l y.1.l, list_sum_fixed K n x.1 y.1, sum_fst_fixed K n x.1 y.1⟩⟩
def vec_zero_coord : aff_coord_vec K n fr := ⟨⟨zero_vector K n, len_zero K n, head_zero K n⟩⟩
def vec_neg_coord : aff_coord_vec K n fr → aff_coord_vec K n fr
| ⟨⟨l, len, fst⟩⟩ := ⟨⟨vecl_neg l, vec_len_neg K n ⟨l, len, fst⟩, head_neg_0 K n ⟨l, len, fst⟩⟩⟩


/-! ### type class instances for the abelian group operations -/
instance : has_add (aff_coord_vec K n fr) := ⟨vec_add_coord K n fr⟩
instance : has_zero (aff_coord_vec K n fr) := ⟨vec_zero_coord K n fr⟩
instance : has_neg (aff_coord_vec K n fr) := ⟨vec_neg_coord K n fr⟩
@[ext]
def vec_scalar_coord : K → aff_coord_vec K n fr → aff_coord_vec K n fr :=
    λ a x, ⟨⟨scalar_mul a x.1.1, trans (scale_len a x.1.1) x.1.2, sorry⟩⟩
/-! ### Type class instance for abelian group -/
instance aff_comm_group_coord : add_comm_group (aff_coord_vec K n fr) :=
begin
    sorry
end
instance : has_scalar K (aff_coord_vec K n fr) := ⟨vec_scalar_coord K n fr⟩

/-
lemma vec_one_smul_coord : (1 : K) • cv1 = cv1 := 
begin
cases cv1,

ext,
split,
intros,
dsimp only [has_scalar.smul, vec_scalar] at a_1,
rw one_smul_cons at a_1,
exact a_1,

intros,
dsimp only [has_scalar.smul, vec_scalar],
rw one_smul_cons,
exact a_1,
end
-/
lemma vec_mul_smul_coord : ∀ g h : K, ∀ x : aff_coord_vec K n fr, (g * h) • x = g • h • x := sorry


instance : mul_action K (aff_coord_vec K n fr) := ⟨sorry, vec_mul_smul_coord K n fr⟩


instance : distrib_mul_action K (aff_coord_vec K n fr) := 
    sorry
instance aff_semimod_coord : semimodule K (aff_coord_vec K n fr)
    --[distrib_mul_action K (aff_coord_vec K n fr)] 
    := 
    -- extremely odd that this doesnt work....
    ⟨sorry, sorry⟩



def aff_group_action_coord : (aff_coord_vec K n fr) → (aff_coord_pt K n fr) → (aff_coord_pt K n fr) :=
    λ x y, ⟨⟨ladd x.1.1 y.1.1, sorry, sorry⟩⟩

def aff_group_sub_coord : (aff_coord_pt K n fr) → (aff_coord_pt K n fr) → (aff_coord_vec K n fr) :=
    λ x y, ⟨⟨ladd x.1.1 (vecl_neg y.1.1), sorry, sorry⟩⟩



instance : has_vadd (aff_coord_vec K n fr) (aff_coord_pt K n fr) := ⟨aff_group_action_coord K n fr⟩

instance : has_vsub (aff_coord_vec K n fr) (aff_coord_pt K n fr) := ⟨aff_group_sub_coord K n fr⟩

instance : add_action (aff_coord_vec K n fr) (aff_coord_pt K n fr) := sorry--⟨aff_group_action K n, aff_zero_sadd K n, aff_add_sadd K n⟩

/-
We need proof that given a frame f, 
⟨ aff_coord_pt f, aff_coord_vec f⟩ is 
an affine space,
-/

/-

def vecptadd := r3_der2_pt1 +ᵥ r3_der2_vec2 --expected : pass
def vecptsub := r3_der2_pt1 -ᵥ r3_der2_vec2 --expected : pass
def ptvecsub := r3_der2_vec2 -ᵥ r3_der2_pt1 -- expected : pass
-/
def pt_plus_vec
    {X : Type u} 
    {K : Type v} 
    {V : Type w} 
    {n : ℕ}
    {ι : Type*}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {fr : affine_tuple_coordinate_frame K n} :
    (aff_coord_pt K n fr) → 
    (aff_coord_vec K n fr) → 
    (aff_coord_pt K n fr) 
| p v := aff_group_action_coord K n fr v p

notation
 pt +ᵥ v := pt_plus_vec pt v
 
def pt_minus_vec
    {X : Type u} 
    {K : Type v} 
    {V : Type w} 
    {n : ℕ}
    {ι : Type*}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {fr : affine_tuple_coordinate_frame K n} :
    (aff_coord_pt K n fr) → 
    (aff_coord_vec K n fr) → 
    (aff_coord_pt K n fr) 
| p v := aff_group_action_coord K n fr (vec_neg_coord K n fr v) p
.
notation
 pt -ᵥ v := pt_minus_vec pt v


def prf : affine_space (aff_coord_vec K n fr) (aff_coord_pt  K n fr) := sorry

instance afc : affine_space 
    (aff_coord_vec K n fr) 
    (aff_coord_pt  K n fr) := 
    prf K n fr


/-
KEEP?
-/

/-
-/

/-
Code to manufacture a standard basis for a given affine space.
-/
abbreviation zero := zero_vector K n

def list.to_basis_vec : fin n → list K := λ x, (zero K n).update_nth (x.1 + 1) 1

lemma len_basis_vec_fixed (x : fin n) : (list.to_basis_vec K n x).length = n + 1 := sorry

lemma head_basis_vec_fixed (x : fin n) : (list.to_basis_vec K n x).head = 0 := sorry

def std_basis : fin n → aff_vec_coord_tuple K n :=
λ x, ⟨list.to_basis_vec K n x, len_basis_vec_fixed K n x, head_basis_vec_fixed K n x⟩

lemma std_is_basis : is_basis K (std_basis K n) := sorry

def aff_coord_space_std_frame : 
    affine_tuple_coordinate_frame K n := 
           ⟨(pt_zero K n) 
           ,(std_basis K n) 
           , (std_is_basis K n)⟩

--affine_frame (aff_coord_pt fr_n) K (aff_coord_pt fr_n) (iota)


end aff_fr