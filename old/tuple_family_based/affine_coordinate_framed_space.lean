import linear_algebra.affine_space.basic
import linear_algebra.basis
import .affine_coordinate_space

open_locale affine

/-
This file contains
affine_tuple_coord_frame
affine_coord_frame
aff_coord_pt
aff_coord_vec
Also all instances necessary. Missing some proofs 11/20
-/


namespace aff_fr

universes u v w

variables 

    (K : Type u)
    (X : Type v)
    (V : Type w)
    [ring K] 
    [add_comm_group V] 
    [module K V]  
    [affine_space V X]

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

/-
An affine frame comprises an origin point
and a basis for the vector space.
-/

#check @aff_pt_coord_tuple

structure affine_tuple_coord_frame :=
(origin : aff_pt_coord_tuple K n) 
(basis : (fin n) → aff_vec_coord_tuple K n) 
(proof_is_basis : is_basis K basis) 

inductive affine_coord_frame
| tuple 
    (base : affine_tuple_coord_frame K n) : affine_coord_frame
| derived 
    (origin : aff_pt_coord_tuple K n) 
    (basis : (fin n) → aff_vec_coord_tuple K n) 
    (proof_is_basis : is_basis K basis) 
    (base : affine_coord_frame)
    : affine_coord_frame

@[ext]
structure aff_coord_pt (fr : affine_coord_frame K n) 
            extends aff_pt_coord_tuple K n :=
   mk ::

@[ext]
structure aff_coord_vec (fr : affine_coord_frame K n) 
            extends aff_vec_coord_tuple K n  :=
   mk ::

variables 
    (fr : affine_coord_frame K n) 
    (cv1 cv2 : aff_coord_vec K n fr) 
    (cp1 cp2 : aff_coord_pt  K n fr)

def pt_zero_coord : aff_coord_pt K n fr := ⟨aff_pt_tuple_zero K n⟩

def zero_vector_coord : aff_coord_vec K n fr := ⟨aff_vec_tuple_zero K n⟩

#check vec_add
/-! ### abelian group operations -/
def vec_add_coord : aff_coord_vec K n fr → aff_coord_vec K n fr → aff_coord_vec K n fr :=
    λ x y, ⟨vec_add K n x.1 y.1⟩
def vec_zero_coord : aff_coord_vec K n fr := ⟨⟨zero_vector K n, len_zero K n, head_zero K n⟩⟩
def vec_neg_coord : aff_coord_vec K n fr → aff_coord_vec K n fr
| ⟨⟨l, len, fst⟩⟩ := ⟨⟨vecl_neg l, vec_len_neg K n ⟨l, len, fst⟩, head_neg_0 K n ⟨l, len, fst⟩⟩⟩

/-! ### type class instances for the abelian group operations -/
instance : has_add (aff_coord_vec K n fr) := ⟨vec_add_coord K n fr⟩
instance : has_zero (aff_coord_vec K n fr) := ⟨vec_zero_coord K n fr⟩
instance : has_neg (aff_coord_vec K n fr) := ⟨vec_neg_coord K n fr⟩

-- properties necessary to show aff_vec_coord_tuple K n is an instance of add_comm_group
#print add_comm_group
lemma vec_add_assoc_coord : ∀ x y z : aff_coord_vec K n fr,  x + y + z = x + (y + z) :=
begin
intros,
induction x,
induction y,
induction z,
cases x,
cases y,
cases z,
ext,
split,
intro a_1,
dsimp [has_add.add, vec_add_coord, vec_add] at a_1,
--dsimp [has_add.add, vec_add, vec_add_coord] at a_1,
rw ladd_assoc at a_1,
exact a_1,

intro a_1,
dsimp [has_add.add, vec_add_coord, vec_add] at a_1 ⊢,
rw ladd_assoc,
exact a_1
end

lemma vec_zero_is_coord : (0 : aff_coord_vec K n fr) = vec_zero_coord K n fr := rfl

lemma vec_zero_add_coord : ∀ x : aff_coord_vec K n fr, 0 + x = x :=
begin
intro x,
induction x,
cases x,
rw vec_zero_is_coord,
ext,
split,
intro a_1,
dsimp [has_add.add, vec_add, vec_zero] at a_1,
change a ∈ (ladd (zero_vector K n) x_l).nth n_1 at a_1,
rw zero_ladd' x_l n x_len_fixed at a_1,
exact a_1,

intro a_1,
dsimp [has_add.add, vec_add, vec_zero],
change a ∈ (ladd (zero_vector K n) x_l).nth n_1,
rw zero_ladd' x_l n x_len_fixed,
exact a_1,
end

lemma vec_add_zero_coord : ∀ x : aff_coord_vec K n fr, x + 0 = x :=
begin
intro x,
induction x,
cases x,
rw vec_zero_is_coord,
ext,
split,
intro a_1,
dsimp [has_add.add, vec_add, vec_zero] at a_1,
change a ∈ (ladd x_l (zero_vector K n)).nth n_1 at a_1,
rw ladd_zero' x_l n x_len_fixed at a_1,
exact a_1,

intro a_1,
dsimp [has_add.add, vec_add, vec_zero],
change a ∈ (ladd x_l (zero_vector K n)).nth n_1,
rw ladd_zero' x_l n x_len_fixed,
exact a_1,
end

lemma vec_add_left_neg_coord : ∀ x : aff_coord_vec K n fr, -x + x = 0 :=
begin
intro x,
induction x,
cases x,
rw vec_zero_is_coord,
ext,
split,
intro a_1,
dsimp [vec_zero_coord],
dsimp [has_neg.neg, vec_neg_coord, vec_neg, has_add.add, vec_add_coord,vec_add] at a_1,
cases x_l,
contradiction,
rw [ladd_left_neg, x_len_fixed] at a_1,
exact a_1,
contradiction,

intro a_1,
dsimp [vec_zero_coord] at a_1,
dsimp [has_neg.neg, vec_neg_coord, vec_neg, has_add.add, vec_add_coord, vec_add],
cases x_l,
contradiction,
rw [ladd_left_neg, x_len_fixed],
exact a_1,
contradiction
end

lemma vec_add_comm_coord : ∀ x y : aff_coord_vec K n fr, x + y = y + x :=
begin
intros x y,
induction x,
cases x,
induction y,
cases y,
ext,
split,
intro a_1,
dsimp [has_add.add, vec_add_coord, vec_add] at a_1 ⊢,
rw ladd_comm,
exact a_1,

intro a_1,
dsimp [has_add.add, vec_add_coord, vec_add] at a_1 ⊢,
rw ladd_comm,
exact a_1,
end

/-! ### Type class instance for abelian group -/
instance aff_comm_group_coord : add_comm_group (aff_coord_vec K n fr) :=
begin
split,
exact vec_add_left_neg_coord K n fr,
exact vec_add_comm_coord K n fr,
exact vec_add_assoc_coord K n fr,
exact vec_zero_add_coord K n fr,
exact vec_add_zero_coord K n fr,
end



/-! ### Scalar action -/

@[ext]
def vec_scalar_coord : K → aff_coord_vec K n fr → aff_coord_vec K n fr :=
    λ a x, ⟨vec_scalar K n a x.1⟩

instance : has_scalar K (aff_coord_vec K n fr) := ⟨vec_scalar_coord K n fr⟩

lemma vec_one_smul_coord : (1 : K) • cv1 = cv1 := 
begin
induction cv1,
cases cv1,
ext,
split,
intro a_1,
dsimp only [has_scalar.smul, vec_scalar_coord, vec_scalar] at a_1,
rw one_smul_cons at a_1,
exact a_1,

intro a_1,
dsimp only [has_scalar.smul, vec_scalar_coord, vec_scalar],
rw one_smul_cons,
exact a_1,
end

lemma vec_mul_smul_coord : ∀ g h : K, ∀ x : aff_coord_vec K n fr, (g * h) • x = g • h • x :=
begin
intros,
induction x,
cases x,
ext,
split,
intro a_1,
dsimp only [has_scalar.smul, vec_scalar_coord, vec_scalar] at a_1 ⊢,
rw vecl.smul_assoc at a_1,
exact a_1,

intro a_1,
dsimp only [has_scalar.smul, vec_scalar_coord, vec_scalar] at a_1 ⊢,
rw vecl.smul_assoc,
exact a_1
end

instance : mul_action K (aff_coord_vec K n fr) := ⟨vec_one_smul_coord K n fr, vec_mul_smul_coord K n fr⟩

lemma vec_smul_add_coord : ∀ g : K, ∀ x y : aff_coord_vec K n fr, g • (x + y) = g•x + g•y :=
begin
intros,
induction x,
cases x,
induction y,
cases y,
ext,
dsimp only [has_scalar.smul, vec_scalar_coord, vec_scalar, has_add.add, vec_add_coord, vec_add],
split,
intro a_1,
rw smul_ladd at a_1,
exact a_1,

intro a_1,
rw smul_ladd,
exact a_1
end

lemma vec_smul_zero_coord : ∀ g : K, g • (0 : aff_coord_vec K n fr) = 0 :=
begin
intros,
rw vec_zero_is_coord,
dsimp [vec_zero_coord],
ext,
split,
intro a_1,
dsimp only [has_scalar.smul, vec_scalar_coord, vec_scalar] at a_1 ⊢,
rw smul_zero_cons at a_1,
exact a_1,

intro a_1,
dsimp only [has_scalar.smul, vec_scalar_coord, vec_scalar] at a_1 ⊢,
rw smul_zero_cons,
exact a_1
end

instance : distrib_mul_action K (aff_coord_vec K n fr) := ⟨vec_smul_add_coord K n fr, vec_smul_zero_coord K n fr⟩

lemma vec_add_smul_coord : ∀ g h : K, ∀ x : aff_coord_vec K n fr, (g + h) • x = g•x + h•x :=
begin
intros,
have h₁ : distrib.add g h = g + h := rfl,
induction x,
cases x,
ext,
split,
intro a_1,
dsimp only [has_scalar.smul, vec_scalar_coord, vec_scalar, has_add.add, vec_add_coord, vec_add] at a_1 ⊢,
rw [h₁, ladd_smul] at a_1,
exact a_1,

intro a_1,
dsimp only [has_scalar.smul, vec_scalar_coord, vec_scalar, has_add.add, vec_add_coord, vec_add] at a_1 ⊢,
rw [h₁, ladd_smul],
exact a_1
end

lemma vec_zero_smul_coord : ∀ x : aff_coord_vec K n fr, (0 : K) • x = 0 :=
begin
intros,
induction x,
cases x,
ext,
split,
intro a_1,
dsimp [has_scalar.smul, vec_scalar_coord, vec_scalar] at a_1,
rw [zero_smul_cons, x_len_fixed] at a_1,
rw vec_zero_is_coord,
exact a_1,
intro bad,
have len_zero : x_l.length = 0 := by {rw bad, refl},
have nat_succ_n_zero : n + 1 ≠ 0 := by contradiction,
rw eq.symm x_len_fixed at nat_succ_n_zero,
contradiction,

intro a_1,
dsimp [has_scalar.smul, vec_scalar_coord, vec_scalar],
rw [zero_smul_cons, x_len_fixed],
rw vec_zero_is_coord at a_1,
exact a_1,
intro bad,
have len_zero : x_l.length = 0 := by {rw bad, refl},
have nat_succ_n_zero : n + 1 ≠ 0 := by contradiction,
rw eq.symm x_len_fixed at nat_succ_n_zero,
contradiction
end

instance aff_semimod_coord : semimodule K (aff_coord_vec K n fr) := ⟨vec_add_smul_coord K n fr, vec_zero_smul_coord K n fr⟩

instance aff_module_coord : module K (aff_coord_vec K n fr) := ⟨vec_add_smul_coord K n fr, vec_zero_smul_coord K n fr⟩

/-! ### group action of aff_vec_coord_tuple on aff_pt_coord_tuple -/

def aff_group_action_coord : aff_coord_vec K n fr → aff_coord_pt K n fr → aff_coord_pt K n fr :=
    λ x y, ⟨aff_group_action K n x.1 y.1⟩


def aff_group_sub_coord : aff_coord_pt K n fr → aff_coord_pt K n fr → aff_coord_vec K n fr :=
    λ x y, ⟨aff_group_sub K n x.1 y.1⟩

#check add_action

instance : has_vadd (aff_coord_vec K n fr) (aff_coord_pt K n fr) := ⟨aff_group_action_coord K n fr⟩

instance : has_vsub (aff_coord_vec K n fr) (aff_coord_pt K n fr) := ⟨aff_group_sub_coord K n fr⟩

lemma aff_zero_sadd_coord : ∀ x : aff_coord_pt K n fr, (0 : aff_coord_vec K n fr) +ᵥ x = x :=
begin
intros,
rw vec_zero_is_coord,
induction x,
cases x,
have h₁ : n = length x_l - 1 := by {rw x_len_fixed, refl},
dsimp [vec_zero_coord],
ext,
split,
intro a_1,
dsimp [has_vadd.vadd, aff_group_action_coord, aff_group_action] at a_1 ⊢,
rw [h₁, zero_ladd] at a_1,
exact a_1,

intro a_1,
dsimp [has_vadd.vadd, aff_group_action_coord, aff_group_action] at a_1 ⊢,
rw [h₁, zero_ladd],
exact a_1
end

lemma aff_add_sadd_coord : ∀ x y : aff_coord_vec K n fr, ∀ a : aff_coord_pt K n fr, x +ᵥ (y +ᵥ a) = x + y +ᵥ a :=
begin
intros,
induction x,
cases x,
induction y,
cases y,
induction a,
cases a,
ext,
dsimp [has_vadd.vadd, aff_group_action_coord, aff_group_action, has_add.add, vec_add_coord, vec_add],
split,
intro a_1,
rw ladd_assoc,
exact a_1,

intro a_1,
rw ladd_assoc at a_1,
exact a_1
end

instance : add_action (aff_coord_vec K n fr) (aff_coord_pt K n fr) := ⟨aff_group_action_coord K n fr, aff_zero_sadd_coord K n fr, aff_add_sadd_coord K n fr⟩

lemma aff_add_trans_coord : ∀ a b : aff_coord_pt K n fr, ∃ x : aff_coord_vec K n fr, x +ᵥ a = b :=
begin
intros,
fapply exists.intro,
exact b -ᵥ a,
induction a,
cases a,
induction b,
cases b,
have h₁ : a_l.length = b_l.length := by {transitivity, exact a_len_fixed, symmetry, exact b_len_fixed},
have h₂ : a_l ≠ nil :=
    begin
    intro bad,
    rw bad at a_len_fixed,
    contradiction
    end,
ext,
dsimp [has_vsub.vsub, aff_group_sub_coord, aff_group_sub, has_vadd.vadd, aff_group_action_coord, aff_group_action],
split,
intro a_1,
rw [ladd_assoc, ladd_left_neg, h₁, ladd_zero] at a_1,
exact a_1,
exact h₂,

intro a_1,
rw [ladd_assoc, ladd_left_neg, h₁, ladd_zero],
exact a_1,
exact h₂
end

lemma aff_add_free_coord : ∀ a : aff_coord_pt K n fr, ∀ g h : aff_coord_vec K n fr, g +ᵥ a = h +ᵥ a → g = h :=
begin
intros a g h h₀,
--simp [] at h₀ ,
--dsimp [has_vadd.vadd, aff_group_action] at h₀,
have h₁ : a.1.1.length = g.1.1.length := eq.trans a.1.2 (eq.symm g.1.2),
have h₂ : a.1.1.length = h.1.1.length := eq.trans a.1.2 (eq.symm h.1.2),
have h₃ : a.1.1 ≠ nil := by {have a_len_fixed := a.1.2, intro bad, rw bad at a_len_fixed, contradiction},
have h₄ : (g +ᵥ a).1.1 = (h +ᵥ a).1.1 := by
        rw h₀
    ,
have h₅ := ladd_free g.1.1 h.1.1 a.1.1 h₁ h₂ h₃ h₄,
ext,
split,
intro a_1,
rw h₅ at a_1,
exact a_1,

intro a_1,
rw h₅,
exact a_1,
end

lemma aff_vadd_vsub_coord : ∀ (x : aff_coord_vec K n fr) (a : aff_coord_pt K n fr), x +ᵥ a -ᵥ a = x := 
begin
intros,
induction x,
cases x,
induction a,
cases a,
have h₁ : ladd a_l (vecl_neg a_l) = ladd (vecl_neg a_l) a_l := by rw ladd_comm,
have h₂ : a_l.length = x_l.length := eq.trans a_len_fixed (eq.symm x_len_fixed),
have h₃ : a_l ≠ nil := by {intro bad, rw bad at a_len_fixed, contradiction},

ext,
dsimp [has_vadd.vadd, aff_group_action_coord, aff_group_action, has_vsub.vsub, aff_group_sub_coord, aff_group_sub],
split,
intro a_1,
rw [ladd_assoc, h₁, ladd_left_neg, h₂, ladd_zero] at a_1,
exact a_1,
exact h₃,

intro a_1,
rw [ladd_assoc, h₁, ladd_left_neg, h₂, ladd_zero],
exact a_1,
exact h₃
end

lemma aff_vsub_vadd_coord : ∀ a b : aff_coord_pt K n fr, (a -ᵥ b) +ᵥ b = a :=
begin
intros,
induction a,
cases a,
induction b,
cases b,
have h₁ : b_l.length = a_l.length := eq.trans b_len_fixed (eq.symm a_len_fixed),
have h₂ : b_l ≠ nil := by {intro bad, rw bad at b_len_fixed, contradiction},
ext,
dsimp [has_vsub.vsub, aff_group_sub_coord, aff_group_sub, has_vadd.vadd, aff_group_action_coord, aff_group_action],
split,
intro a_1,
rw [ladd_assoc, ladd_left_neg, h₁, ladd_zero] at a_1,
exact a_1,
exact h₂,

intro a_1,
rw [ladd_assoc, ladd_left_neg, h₁, ladd_zero],
exact a_1,
exact h₂
end

instance : nonempty (aff_coord_pt K n fr) := ⟨⟨pt_zero K n⟩⟩

instance aff_torsor_coord : add_torsor (aff_coord_vec K n fr) (aff_coord_pt K n fr) := 
⟨aff_group_action_coord K n fr, 
aff_zero_sadd_coord K n fr,
aff_add_sadd_coord K n fr,
aff_group_sub_coord K n fr,
aff_vsub_vadd_coord K n fr, 
aff_vadd_vsub_coord K n fr⟩

/-
"THEOREM:" these sets of scalar tuples with the operations defined on them
do have the structure of an affine space.
-/

instance aff_coord_is : 
    affine_space 
        (aff_coord_vec K n fr) 
        (aff_coord_pt K n fr) := 
    ⟨aff_group_action_coord K n fr, 
aff_zero_sadd_coord K n fr,
aff_add_sadd_coord K n fr,
aff_group_sub_coord K n fr,
aff_vsub_vadd_coord K n fr, 
aff_vadd_vsub_coord K n fr⟩

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
    {fr : affine_coord_frame K n} :
    (aff_coord_pt K n fr) → 
    (aff_coord_vec K n fr) → 
    (aff_coord_pt K n fr) 
| p v := aff_group_action_coord K n fr v p

notation
 pt +ᵥ v := pt_plus_vec pt v

 
def vec_mul_scalar
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
    {fr : affine_coord_frame K n} :
    (aff_coord_vec K n fr) → 
    K → 
    (aff_coord_vec K n fr) 
| v s := s • v

notation
 v • s := vec_mul_scalar v s
 
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
    {fr : affine_coord_frame K n} :
    (aff_coord_pt K n fr) → 
    (aff_coord_vec K n fr) → 
    (aff_coord_pt K n fr) 
| p v := aff_group_action_coord K n fr (vec_neg_coord K n fr v) p

notation
 pt -ᵥ v := pt_minus_vec pt v

end aff_fr