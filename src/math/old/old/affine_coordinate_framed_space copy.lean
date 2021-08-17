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
structure affine_frame  :=
(origin : X) 
(basis : ι → V) 
(proof_is_basis : is_basis K basis)

#check affine_frame
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

structure aff_coord_pt (fr : affine_frame X K V ι) extends aff_pt_coord_tuple K n :=
   -- (tuple : aff_pt_coord_tuple K n)
   mk ::

structure aff_coord_vec (fr : affine_frame X K V ι) extends aff_vec_coord_tuple K n  :=
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
    (fr : affine_frame X K V ι) 
    (cv1 cv2 : aff_coord_vec X K V n ι fr) 
    (cp1 cp2 : aff_coord_pt  X K V n ι fr)

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
def vec_add_coord : aff_coord_vec X K V n ι fr → aff_coord_vec X K V n ι fr → aff_coord_vec X K V n ι fr :=
    λ x y, ⟨⟨ladd x.1.l y.1.l, list_sum_fixed K n x.1 y.1, sum_fst_fixed K n x.1 y.1⟩⟩
def vec_zero_coord : aff_coord_vec X K V n ι fr := ⟨⟨zero_vector K n, len_zero K n, head_zero K n⟩⟩
def vec_neg_coord : aff_coord_vec X K V n ι fr → aff_coord_vec X K V n ι fr
| ⟨⟨l, len, fst⟩⟩ := ⟨⟨vecl_neg l, vec_len_neg K n ⟨l, len, fst⟩, head_neg_0 K n ⟨l, len, fst⟩⟩⟩


/-! ### type class instances for the abelian group operations -/
instance : has_add (aff_coord_vec X K V n ι fr) := ⟨vec_add_coord X K V n ι fr⟩
instance : has_zero (aff_coord_vec X K V n ι fr) := ⟨vec_zero_coord X K V n ι fr⟩
instance : has_neg (aff_coord_vec X K V n ι fr) := ⟨vec_neg_coord X K V n ι fr⟩
@[ext]
def vec_scalar_coord : K → aff_coord_vec X K V n ι fr → aff_coord_vec X K V n ι fr :=
    λ a x, ⟨⟨scalar_mul a x.1.1, trans (scale_len a x.1.1) x.1.2, sorry⟩⟩
/-! ### Type class instance for abelian group -/
instance aff_comm_group_coord : add_comm_group (aff_coord_vec X K V n ι fr) :=
begin
    sorry
end
instance : has_scalar K (aff_coord_vec X K V n ι fr) := ⟨vec_scalar_coord X K V n ι fr⟩

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
lemma vec_mul_smul_coord : ∀ g h : K, ∀ x : aff_coord_vec X K V n ι fr, (g * h) • x = g • h • x := sorry


instance : mul_action K (aff_coord_vec X K V n ι fr) := ⟨sorry, vec_mul_smul_coord X K V n ι fr⟩


instance : distrib_mul_action K (aff_coord_vec X K V n ι fr) := 
    sorry
instance aff_semimod_coord : semimodule K (aff_coord_vec X K V n ι fr)
    --[distrib_mul_action K (aff_coord_vec X K V n ι fr)] 
    := 
    -- extremely odd that this doesnt work....
    ⟨sorry, sorry⟩



def aff_group_action_coord : (aff_coord_vec X K V n ι fr) → (aff_coord_pt X K V n ι fr) → (aff_coord_pt X K V n ι fr) :=
    λ x y, ⟨⟨ladd x.1.1 y.1.1, sorry, sorry⟩⟩

def aff_group_sub_coord : (aff_coord_pt X K V n ι fr) → (aff_coord_pt X K V n ι fr) → (aff_coord_vec X K V n ι fr) :=
    λ x y, ⟨⟨ladd x.1.1 (vecl_neg y.1.1), sorry, sorry⟩⟩



instance : has_vadd (aff_coord_vec X K V n ι fr) (aff_coord_pt X K V n ι fr) := ⟨aff_group_action_coord X K V n ι fr⟩

instance : has_vsub (aff_coord_vec X K V n ι fr) (aff_coord_pt X K V n ι fr) := ⟨aff_group_sub_coord X K V n ι fr⟩

instance : add_action (aff_coord_vec X K V n ι fr) (aff_coord_pt X K V n ι fr) := sorry--⟨aff_group_action K n, aff_zero_sadd K n, aff_add_sadd K n⟩

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
    {fr : affine_frame X K V ι} :
    (aff_coord_pt X K V n ι fr) → 
    (aff_coord_vec X K V n ι fr) → 
    (aff_coord_pt X K V n ι fr) 
| p v := aff_group_action_coord X K V n ι fr v p

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
    {fr : affine_frame X K V ι} :
    (aff_coord_pt X K V n ι fr) → 
    (aff_coord_vec X K V n ι fr) → 
    (aff_coord_pt X K V n ι fr) 
| p v := aff_group_action_coord X K V n ι fr (vec_neg_coord X K V n ι fr v) p
.
notation
 pt -ᵥ v := pt_minus_vec pt v


def prf : affine_space (aff_coord_vec X K V n ι fr) (aff_coord_pt  X K V n ι fr) := sorry

instance afc : affine_space 
    (aff_coord_vec X K V n ι fr) 
    (aff_coord_pt  X K V n ι fr) := 
    prf X K V n ι fr


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
    affine_frame (aff_pt_coord_tuple K n) K (aff_vec_coord_tuple K n) (fin n) := 
        ⟨pt_zero K n, std_basis K n, std_is_basis K n⟩

--affine_frame (aff_coord_pt fr_n) K (aff_coord_pt fr_n) (iota)


def aff_tuple_frame 
    :=
    affine_frame 
        (aff_pt_coord_tuple K n) K (aff_vec_coord_tuple K n) (fin n)

def aff_tuple_framed_pt (f : aff_tuple_frame K n) :=
    aff_coord_pt (aff_pt_coord_tuple K n) K (aff_vec_coord_tuple K n) n (fin n) f

def aff_tuple_framed_vec (f : aff_tuple_frame K n) :=
    aff_coord_vec (aff_pt_coord_tuple K n) K (aff_vec_coord_tuple K n) n (fin n) f

instance a1 (fr : aff_tuple_frame K n): has_add (aff_tuple_framed_vec K n fr) := sorry
instance a2 (fr : aff_tuple_frame K n): has_zero (aff_tuple_framed_vec K n fr) := sorry
instance a3 (fr : aff_tuple_frame K n): has_neg (aff_tuple_framed_vec K n fr) := sorry
instance a4 (fr : aff_tuple_frame K n): add_comm_group (aff_tuple_framed_vec K n fr) := sorry
instance a5 (fr : aff_tuple_frame K n) : has_scalar K (aff_tuple_framed_vec K n fr) := sorry
instance a6 (fr : aff_tuple_frame K n) : mul_action K (aff_tuple_framed_vec K n fr) := 
    ⟨sorry, sorry⟩
instance a7 (fr : aff_tuple_frame K n) : distrib_mul_action K (aff_tuple_framed_vec K n fr) := 
    sorry
instance a8 (fr : aff_tuple_frame K n) : semimodule K (aff_tuple_framed_vec K n fr)
    := ⟨sorry, sorry⟩
instance a9 (fr : aff_tuple_frame K n)  : has_vadd (aff_tuple_framed_vec K n fr) (aff_tuple_framed_pt K n fr) := sorry
instance a10 (fr : aff_tuple_frame K n)  : has_vsub (aff_tuple_framed_vec K n fr) (aff_tuple_framed_pt K n fr) := sorry
instance a11 (fr : aff_tuple_frame K n)  : add_action (aff_tuple_framed_vec K n fr) (aff_tuple_framed_pt K n fr) := sorry--⟨aff_group_action K n, aff_zero_sadd K n, aff_add_sadd K n⟩
instance a12 (fr : aff_tuple_frame K n)  : affine_space 
    (aff_tuple_framed_vec K n fr) 
    (aff_tuple_framed_pt K n fr) := 
    sorry

inductive fr_type (t : Type) : Type → Type
| fr1 : fr_type t

def aff_tuple_framed_frame
    (f : aff_tuple_frame K n)
    :=
    affine_frame 
        (aff_tuple_framed_pt K n f) K (aff_tuple_framed_vec K n f) (fin n)

def aff_quasi_framed_pt 
    {f : aff_tuple_frame K n}
    (fr : aff_tuple_framed_frame K n f) :=
    aff_coord_pt (aff_pt_coord_tuple K n) K (aff_vec_coord_tuple K n) n (fin n) f

def aff_quasi_framed_vec
    {f : aff_tuple_frame K n}
    (fr : aff_tuple_framed_frame K n f) :=
    aff_coord_vec (aff_pt_coord_tuple K n) K (aff_vec_coord_tuple K n) n (fin n) f


instance a21 {f : aff_tuple_frame K n} (fr : aff_tuple_framed_frame K n f): has_add (aff_quasi_framed_vec K n fr) := sorry
instance a22 {f : aff_tuple_frame K n} (fr : aff_tuple_framed_frame K n f): has_zero (aff_quasi_framed_vec K n fr)  := sorry
instance a23 {f : aff_tuple_frame K n} (fr : aff_tuple_framed_frame K n f): has_neg (aff_quasi_framed_vec K n fr)  := sorry
instance a24 {f : aff_tuple_frame K n} (fr : aff_tuple_framed_frame K n f): add_comm_group (aff_quasi_framed_vec K n fr) := sorry
instance a25 {f : aff_tuple_frame K n} (fr : aff_tuple_framed_frame K n f): has_scalar K (aff_quasi_framed_vec K n fr) := sorry
instance a26 {f : aff_tuple_frame K n} (fr : aff_tuple_framed_frame K n f) : mul_action K (aff_quasi_framed_vec K n fr) := 
    ⟨sorry, sorry⟩
instance a27 {f : aff_tuple_frame K n} (fr : aff_tuple_framed_frame K n f): distrib_mul_action K (aff_quasi_framed_vec K n fr) := 
    sorry
instance a28 {f : aff_tuple_frame K n} (fr : aff_tuple_framed_frame K n f) : semimodule K (aff_quasi_framed_vec K n fr)
    := ⟨sorry, sorry⟩
instance a29 {f : aff_tuple_frame K n} (fr : aff_tuple_framed_frame K n f) : has_vadd (aff_quasi_framed_vec K n fr) (aff_quasi_framed_pt K n fr) := sorry
instance a210 {f : aff_tuple_frame K n} (fr : aff_tuple_framed_frame K n f) : has_vsub (aff_quasi_framed_vec K n fr) (aff_quasi_framed_pt K n fr) := sorry
instance a211 {f : aff_tuple_frame K n} (fr : aff_tuple_framed_frame K n f) : add_action (aff_quasi_framed_vec K n fr) (aff_quasi_framed_pt K n fr) := sorry--⟨aff_group_action K n, aff_zero_sadd K n, aff_add_sadd K n⟩
instance a212 {f : aff_tuple_frame K n} (fr : aff_tuple_framed_frame K n f): affine_space 
    (aff_quasi_framed_vec K n fr) 
    (aff_quasi_framed_pt K n fr) := 
    sorry

def aff_quasi_frame

end aff_fr