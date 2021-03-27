-- aliases


-- OPERATIONS

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
      

def vec_neg (v : aff_vec_coord_tuple K n) : aff_vec_coord_tuple K n :=
vec_scalar_mul K n (-1:K) v
/-
used to be ...
| ⟨l, len, fst⟩ := ⟨vecl_neg l, vec_len_neg K n ⟨l, len, fst⟩, head_neg_0 K n ⟨l, len, fst⟩⟩
-/


-- OVERLOADED OPERATORS

/-! ### type class instances for the abelian group operations -/
instance : has_add (aff_vec_coord_tuple K n) := ⟨vec_add K n⟩
instance : has_zero (aff_vec_coord_tuple K n) := ⟨vec_zero K n⟩
instance : has_neg (aff_vec_coord_tuple K n) := ⟨vec_neg K n⟩


-- PROPERTIES

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
   ⟨aff_group_action K n, aff_zero_sadd K n, aff_add_sadd K n⟩

lemma aff_add_trans : 
∀ (a b : aff_pt_coord_tuple K n), 
  ∃ x : aff_vec_coord_tuple K n, x +ᵥ a = b := sorry

lemma aff_add_free : 
∀ (a : aff_pt_coord_tuple K n) (g h : aff_vec_coord_tuple K n), 
  g +ᵥ a = h +ᵥ a → g = h := sorry

-- TODO: Fix problem with -ᵥ notation
lemma aff_vadd_vsub : 
∀ (x : aff_vec_coord_tuple K n) (a : aff_pt_coord_tuple K n), 
--  (x +ᵥ a) -ᵥ a = x := sorry
  aff_group_sub K n (x +ᵥ a)  a = x := sorry

-- TODO: Fix problem with -ᵥ notation
lemma aff_vsub_vadd : ∀ a b : aff_pt_coord_tuple K n, 
  (aff_group_sub K n a b) +ᵥ b = a := sorry


/-
NON-EMPTY
-/

instance : nonempty (aff_pt_coord_tuple K n) := ⟨aff_pt_tuple_zero K n⟩

-- still need aff_zero_sadd, aff_add_sadd, aff_vsub_vadd, aff_vadd_vsub

instance aff_torsor : 
  add_torsor 
    (aff_vec_coord_tuple K n) 
    (aff_pt_coord_tuple K n) := 
⟨
  aff_group_action K n, 
  aff_zero_sadd K n,
  aff_add_sadd K n,
  aff_group_sub K n,
  aff_vsub_vadd K n, 
  aff_vadd_vsub K n
⟩

open_locale affine

instance aff_coord_is : 
      affine_spc 
          (aff_vec_coord_tuple K n) 
          (aff_pt_coord_tuple K n) := 
      aff_torsor K n