import data.real.basic
import linear_algebra.affine_space.basic
import linear_algebra.basis
open_locale affine

universes u v w

/-
A version of the unit type that can
live in any type universe. Adds type
universe parameter to usual unit type.
-/

inductive uunit : Type u
| star


structure affine_space_type
    --(id : ℕ)
    (K : Type u)
    (X : Type v)
    (V : Type w)
    [ring K] 
    [add_comm_group V] 
    [module K V]  
    [affine_space V X]

variables 
(K : Type) [ring K] [inhabited K] 
{α : Type v} [has_add α]
-- (n : ℕ) -- no longer assume fix n in this file
-- (a b : α) (al bl : list α)
-- (x y : K) (xl yl : list K)


/- 
      TUPLE MODULE
-/


def tuple : nat → Type u
| 0 := uunit
| (n' + 1) := K × (tuple n')

/-
Note: The tuple type builder takes the following
arguments
K             -- explicit
[ring K]      -- implicit
[inhabited K] -- implicit
n             -- explicit
-/
#check @tuple

def tuple_add : 
  Π {n : nat}, tuple K n → tuple K n → tuple K n
| 0 t1 t2 := uunit.star
| (n' + 1) (h, t) (h', t') := (h + h', tuple_add t t')

def tuple_scalar_mul : Π {n : nat}, K → tuple K n → tuple K n
| 0 _ _ := uunit.star
| (n' + 1) k (h,t) := (h*k, tuple_scalar_mul k t)

def tuple_negate : Π {n : nat}, tuple K n → tuple K n
| _ t := tuple_scalar_mul K (-1:K) t

def tuple_zero : Π (n : nat), @tuple K _ _ n
| 0 := uunit.star
| (n' + 1) := (0, tuple_zero n')

def tuple_head : Π {n : nat}, (n > 0) → tuple K n → K
| 0 _ _ := 0  -- can't happen
| (n' + 1) _ (h,t) := h

def tuple_tail : Π {n : nat}, (n > 0) → tuple K n → tuple K (n-1)
| 0 _ _ := uunit.star  -- can't happen
| (n' + 1) _ (h,t) := t

lemma tuple_heads_add_to_head : ∀ (h k : K) (n : nat) (t1 t2 : tuple K n) (gtz : n > 0),
  tuple_head K gtz t1 = h → 
  tuple_head K gtz t2 = k → 
  tuple_head K gtz (tuple_add K t1 t2) = (h + k) :=
begin
  intros h k n t1 t2 gtz t1h t2k,
  cases n,
  cases gtz,
  cases t1 with t1h t1t,
  cases t2 with t2h t2t,
  simp [tuple_head] at t1h,
  simp [tuple_head] at t2k,
  rw t1h,
  rw t2k,
  simp [tuple_add],
  simp [tuple_head],
end

lemma tuple_zero_heads_add_to_zero_head : ∀ (n : nat) (t1 t2 : tuple K n) (gtz : n > 0),
  tuple_head K gtz t1 = 0 → 
  tuple_head K gtz t2 = 0 → 
  tuple_head K gtz (tuple_add K t1 t2) = 0 + 0 :=
begin
apply tuple_heads_add_to_head K 0 0,
end

/-
    AFFINE COORDINATE TUPLE MODULE
-/

variable (n : nat)

@[ext]
structure aff_vec_coord_tuple :=
  (tup : tuple K (n+1))
  (inv : tuple_head K (by simp) tup = 0)

@[ext]
structure aff_pt_coord_tuple :=
  (tup : tuple K (n+1))
  (inv : tuple_head K (by simp) tup = 1)


/-! ### scalar action -/

def vec_scalar_mul : K → aff_vec_coord_tuple K n → aff_vec_coord_tuple K n
  | k t := aff_vec_coord_tuple.mk (tuple_scalar_mul K k t.tup) sorry 
instance : has_scalar K (aff_vec_coord_tuple K n) := ⟨vec_scalar_mul K n⟩


/-! ### abelian group operations -/

def vec_add : 
  aff_vec_coord_tuple K n → aff_vec_coord_tuple K n → aff_vec_coord_tuple K n
| (aff_vec_coord_tuple.mk t1 fstz1) (aff_vec_coord_tuple.mk t2 fstz2) := 
    aff_vec_coord_tuple.mk 
      (tuple_add K t1 t2)
      begin
        cases t1, cases t2,
        simp [tuple_head] at fstz1; rw fstz1,
        simp [tuple_head] at fstz2; rw fstz2,
        simp [tuple_add, tuple_head]
      end
      

def aff_vec_tuple_zero : aff_vec_coord_tuple K n :=
⟨ tuple_zero K (n+1), rfl ⟩ 
def vec_zero : aff_vec_coord_tuple K n := aff_vec_tuple_zero K n


def vec_neg (v : aff_vec_coord_tuple K n) : aff_vec_coord_tuple K n :=
vec_scalar_mul K n (-1:K) v
-- used to be ...
-- | ⟨l, len, fst⟩ := ⟨vecl_neg l, vec_len_neg K n ⟨l, len, fst⟩, head_neg_0 K n ⟨l, len, fst⟩⟩

/-! ### type class instances for the abelian group operations -/
instance : has_add (aff_vec_coord_tuple K n) := ⟨vec_add K n⟩
instance : has_zero (aff_vec_coord_tuple K n) := ⟨vec_zero K n⟩
instance : has_neg (aff_vec_coord_tuple K n) := ⟨vec_neg K n⟩

/- More Stuff -/

lemma vec_add_assoc : 
∀ (x y z : aff_vec_coord_tuple K n), 
  x + y + z = x + (y + z) := sorry

lemma vec_zero_add : 
∀ (x : aff_vec_coord_tuple K n), 
  0 + x = x := sorry

lemma vec_add_zero : 
∀ (x : aff_vec_coord_tuple K n), 
  x + 0 = x := sorry

lemma vec_add_left_neg : 
∀ (x : aff_vec_coord_tuple K n), 
  -x + x = 0 := sorry

lemma vec_add_comm : 
∀ (x y : aff_vec_coord_tuple K n), 
  x + y = y + x := sorry


/-! ### Type class instance for abelian group -/
instance aff_comm_group : 
  add_comm_group (aff_vec_coord_tuple K n) :=
begin
split,
exact vec_add_left_neg K n,
exact vec_add_comm K n,
exact vec_add_assoc K n,
exact vec_zero_add K n,
exact vec_add_zero K n,
end

/- Stuff -/

variable (x : aff_vec_coord_tuple K n)
lemma vec_one_smul : (1 : K) • x = x := sorry
lemma vec_mul_smul : ∀ (g h : K) (x : aff_vec_coord_tuple K n), 
  (g * h) • x = g • h • x := sorry
instance : mul_action K (aff_vec_coord_tuple K n) := 
  ⟨vec_one_smul K n, vec_mul_smul K n⟩
lemma vec_smul_add : ∀ (g : K) (x y : aff_vec_coord_tuple K n), 
  g • (x + y) = g•x + g•y := sorry
  lemma vec_smul_zero : ∀ (g : K), 
    g • (0 : aff_vec_coord_tuple K n) = 0 := sorry
lemma vec_add_smul : ∀ (g h : K) (x : aff_vec_coord_tuple K n), 
  (g + h) • x = g•x + h•x := sorry
lemma vec_zero_smul : ∀ (x : aff_vec_coord_tuple K n), 
  (0 : K) • x = 0 := sorry

instance aff_dist_mul_action: distrib_mul_action K (aff_vec_coord_tuple K n) := 
  ⟨vec_smul_add K n, vec_smul_zero K n⟩
instance aff_semimod : semimodule K (aff_vec_coord_tuple K n) := 
  ⟨vec_add_smul K n, vec_zero_smul K n⟩
instance aff_module : module K (aff_vec_coord_tuple K n) := 
  aff_semimod K n


/-
NEXT
-/

/-
Vectors add on points by displacing them.
-/
def aff_group_action : 
  aff_vec_coord_tuple K n → 
  aff_pt_coord_tuple K n → 
  aff_pt_coord_tuple K n :=
λ vec pt, 
  aff_pt_coord_tuple.mk 
    (tuple_add K vec.tup pt.tup)
    sorry

def aff_group_sub : 
  aff_pt_coord_tuple K n → 
  aff_pt_coord_tuple K n → 
  aff_vec_coord_tuple K n :=
λ pt2 pt1, 
  aff_vec_coord_tuple.mk 
    (tuple_add K pt2.tup (tuple_negate K pt1.tup))
    sorry
--    λ x y, ⟨ladd x.1 (vecl_neg y.1), sub_len_fixed K n x y, sub_fst_fixed K n x y⟩

/-
instance : has_vadd (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n) := ⟨aff_group_action K n⟩
instance : has_vsub (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n) := ⟨aff_group_sub K n⟩
-/
instance : 
  has_vadd 
    (aff_vec_coord_tuple K n) 
    (aff_pt_coord_tuple K n) :=
⟨aff_group_action K n⟩ 

instance : 
  has_vsub 
    (aff_vec_coord_tuple K n) 
    (aff_pt_coord_tuple K n) := 
⟨aff_group_sub K n⟩

lemma aff_zero_sadd : 
  ∀ x : aff_pt_coord_tuple K n, 
    (aff_vec_tuple_zero K n) +ᵥ x = x := sorry

lemma aff_add_sadd : 
  ∀ x y : aff_vec_coord_tuple K n, 
  ∀ a : aff_pt_coord_tuple K n, 
    x +ᵥ (y +ᵥ a) = x + y +ᵥ a := sorry

instance : add_action (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n) :=
   ⟨aff_group_action K, aff_zero_sadd K, aff_add_sadd K⟩

lemma aff_add_trans : ∀ (a b : aff_pt_coord_tuple K n), 
  ∃ x : aff_vec_coord_tuple K n, x +ᵥ a = b := sorry

lemma aff_add_free : 
  ∀ (a : aff_pt_coord_tuple K n) (g h : aff_vec_coord_tuple K n), 
    g +ᵥ a = h +ᵥ a → g = h := sorry

lemma aff_vadd_vsub : 
  ∀ (x : aff_vec_coord_tuple K n) (a : aff_pt_coord_tuple K n), 
    x +ᵥ a -ᵥ a = x := sorry

lemma aff_vsub_vadd : 
  ∀ (a b : aff_pt_coord_tuple K n), 
    (a -ᵥ b) +ᵥ b = a := sorry



/-
NON-EMPTY
-/

def aff_pt_tuple_zero : aff_pt_coord_tuple K n:=
⟨ (1, tuple_zero K n), sorry ⟩ 

instance : nonempty (aff_pt_coord_tuple K n) := ⟨aff_pt_tuple_zero K n⟩

-- still need aff_zero_sadd, aff_add_sadd, aff_vsub_vadd, aff_vadd_vsub

instance aff_torsor : 
  add_torsor 
    (aff_vec_coord_tuple K n) 
    (aff_pt_coord_tuple K n) := 
⟨
  aff_group_action K, 
  aff_zero_sadd K,
  aff_add_sadd K,
  aff_group_sub K,
  aff_vsub_vadd K, 
  aff_vadd_vsub K
⟩


instance aff_coord_is : 
      affine_space 
          (aff_vec_coord_tuple K n) 
          (aff_pt_coord_tuple K n) := 
      aff_torsor K n