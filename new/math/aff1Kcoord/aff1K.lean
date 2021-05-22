--import linear_algebra.affine_space.basic
import ..lin2Kcoord.lin2kcoord
import linear_algebra.affine_space.affine_equiv
import tactic.linarith


universes u 
variables 
(K : Type u) 
[field K]
[inhabited K]

/-
Export affine_space (vec K) (pt K) := aff_pt_torsor K,
with vector_space K (vec K) = semimodule K (vec K).
-/


/-
Objects
-/

-- 1-D *affine* K pt and vec objects rep'd by 2-D linear K tuples
@[ext]
structure pt extends K × K := (inv : fst = 1)
@[simp]
def mk_pt' (p : K × K) (i : p.1 = 1): pt K := @pt.mk K _ _ p i    -- private
@[simp]
def mk_pt (k : K) : pt K  := @pt.mk K _ _ (1, k) rfl              -- exported

def pt_coord (p : pt K) : K := p.to_prod.2


@[ext]
structure vec extends K × K := (inv : fst = 0)
@[simp]
def mk_vec' (p : K × K) (i : p.1 = 0): vec K := @vec.mk K _ _ p i -- private
@[simp]
def mk_vec (k : K) : vec K := @vec.mk K _ _ (0, k) rfl            -- exported

def vec_coord (v : vec K) : K := v.to_prod.2


/-
    ********************
    *** Vector space ***
    ********************
-/


@[simp]
def add_vec_vec (v1 v2 : vec K) : vec K := mk_vec' K (v1.to_prod + v2.to_prod) begin 
    cases v1,
    cases v2,
    simp *,
end

@[simp]
def smul_vec (k : K) (v : vec K) : vec K := mk_vec' K (k • v.to_prod) begin 
    cases v,
    simp *,
end --smul

@[simp]
def neg_vec (v : vec K) : vec K := mk_vec' K ((-1 : K) • v.to_prod) begin 
    cases v,
    simp *,
end --smul
@[simp]
def sub_vec_vec (v2 v1 : vec K) : vec K := add_vec_vec K v2 (neg_vec K v1)  -- v2-v1

/-
class add_semigroup (G : Type u) extends has_add G :=
(add_assoc : ∀ a b c : G, a + b + c = a + (b + c))
-/
--instance has_add_vec : has_add (vec K) := ⟨ add_vec_vec K ⟩
--lemma add_assoc_vec : ∀ a b c : vec K, a + b + c = a + (b + c) := sorry
/-begin
    intros,
    dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, division_ring.add, field.add],
    cases a,
    cases b,
    cases c,
    simp *,
    cc
end-/
--instance add_semigroup_vec : add_semigroup (vec K) := ⟨ add_vec_vec K, add_assoc_vec K ⟩ 

/-
has_zero vec
-/
@[simp]
def vec_zero  := mk_vec K 0
instance has_zero_vec : has_zero (vec K) := ⟨vec_zero K⟩

/-
class add_monoid (M : Type u) extends add_semigroup M, has_zero M :=
(zero_add : ∀ a : M, 0 + a = a) (add_zero : ∀ a : M, a + 0 = a)
-/

--lemma zero_add_vec : ∀ a : vec K, 0 + a = a := sorry
/-begin
    intros,
    ext,
    exact zero_add _,
    exact zero_add _,
    /-
    cases a,
    dsimp [has_add.add, add_vec_vec, mk_vec'],
    simp *,
    cases a__to_prod,
    simp *,
    dsimp [a_inv],
    have : a__to_prod_fst = 0 := by exact a_inv,
    simp *,
    exact and.intro (by exact zero_add _) (by exact zero_add _)-/
end-/


--lemma add_zero_vec : ∀ a : vec K, a + 0 = a := sorry
/-begin
    intros,
    ext,
    exact add_zero _,
    exact add_zero _
    --have :  a + 0 = 0 + a := by exact add_comm _ _,
    /-cases a,
    dsimp [has_add.add, add_vec_vec, mk_vec'],
    simp *,
    cases a__to_prod,
    simp *,
    dsimp [a_inv],
    have : a__to_prod_fst = 0 := by exact a_inv,
    simp *,
    
    exact and.intro (by exact zero_add _) (begin 

        --subst add_comm,
        exact add_zero _

    end)-/

end-/

--instance add_monoid_vec : add_monoid (vec K) := sorry
/-⟨ 
    -- add_semigroup
    add_vec_vec K, 
    add_assoc_vec K, 
    -- has_zero
    vec_zero K,
    -- new structure 
    zero_add_vec K, 
    add_zero_vec K
⟩-/


/-
sub_neg_monoid (G : Type u) extends add_monoid G, has_neg G, has_sub G :=
(sub := λ a b, a + -b)
(sub_eq_add_neg : ∀ a b : G, a - b = a + -b . try_refl_tac)
-/
--instance has_neg_vec : has_neg (vec K) := ⟨neg_vec K⟩
--instance has_sub_vec : has_sub (vec K) := ⟨ sub_vec_vec K ⟩ 
--lemma sub_eq_add_neg_vec : ∀ a b : vec K, a - b = a + -b := sorry
/-begin
    intros,
    ext,
    refl,
    refl
end-/

--instance sub_neg_monoid_vec : sub_neg_monoid (vec K) := sorry
/-⟨ 
    add_vec_vec K, add_assoc_vec K, vec_zero K, zero_add_vec K, add_zero_vec K, -- add_monoid
    neg_vec K,                                                                  -- has_neg
    sub_vec_vec K,                                                              -- has_sub
    sub_eq_add_neg_vec K,                                                       -- new
⟩ -/


/-
class add_group (A : Type u) extends sub_neg_monoid A :=
(add_left_neg : ∀ a : A, -a + a = 0)
-/

--lemma add_left_neg_vec : ∀ a : vec K, -a + a = 0 := sorry
/-begin
    intros,
    --ext, 
    --exact
    cases a,
    dsimp [has_neg.neg,neg_vec, mk_vec',sub_neg_monoid.neg, add_group.neg, add_comm_group.neg, ring.neg, division_ring.neg, field.neg],
    simp *,
    cases a__to_prod,
    --cases a.to_prod,
    simp *,
    dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, division_ring.add, field.add],
    simp *,
    have eq0 : a__to_prod_fst = 0 := by exact a_inv,
    subst eq0,
    simp *,

    have : field.add (field.neg 1 * a__to_prod_snd) a__to_prod_snd = 0 := begin
            have negrw : (field.neg 1 * a__to_prod_snd) = -a__to_prod_snd := begin
                dsimp [has_neg.neg,neg_vec, mk_vec',sub_neg_monoid.neg, add_group.neg, add_comm_group.neg, ring.neg, division_ring.neg, field.neg],
                exact neg_one_mul _,
                --subst tor,
            end,
            rw negrw at *,

            exact add_group.add_left_neg _
    end,
    simp *,
    have : (field.add (0:K) (0:K)) = 0 := begin
        exact zero_add _
    end,
    simp *,
    dsimp [has_zero.zero, vec_zero, mk_vec],
    simp *
end-/

--instance : add_group (vec K) :=sorry 
/- ⟨
    -- sub_neg_monoid
    add_vec_vec K, add_assoc_vec K, vec_zero K, zero_add_vec K, add_zero_vec K, -- add_monoid
    neg_vec K,                                                                  -- has_neg
    sub_vec_vec K,                                                              -- has_sub
    sub_eq_add_neg_vec K, 
    -- new
    add_left_neg_vec K,
⟩ -/

/-
Material up to now is needed for affine_space, as defined below. 
The rest of this section is needed for vector_space (vec K).
-/

/-
add_comm_semigroup (G : Type u) extends add_semigroup G :=
(add_comm : ∀ a b : G, a + b = b + a)
-/

--lemma add_comm_vec : ∀ a b : vec K, a + b = b + a := sorry
/-
begin
    intros,
    cases a,
    cases b,
    ext,
    exact add_comm _ _,
    exact add_comm _ _
end
-/
--instance add_comm_semigroup_vec : add_comm_semigroup (vec K) := sorry
/-⟨
    -- add_semigroup
    add_vec_vec K, 
    add_assoc_vec K,
    add_comm_vec K,
⟩-/


/-
/-- An additive commutative monoid is an additive monoid with commutative `(+)`. -/
@[protect_proj, ancestor add_monoid add_comm_semigroup]
class add_comm_monoid (M : Type u) extends add_monoid M, add_comm_semigroup M
attribute [to_additive] comm_monoid
-/

--instance add_comm_monoid_vec : add_comm_monoid (vec K) := sorry
/-⟨
-- add_monoid
    -- add_semigroup
    add_vec_vec K, 
    add_assoc_vec K, 
    -- has_zero
    vec_zero K,
    -- new structure 
    zero_add_vec K, 
    add_zero_vec K,
-- add_comm_semigroup (minus repeats)
    add_comm_vec K,
⟩-/

/-
/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
class has_scalar (α : Type u) (γ : Type v) := (smul : α → γ → γ)
-/
--instance has_scalar_vec : has_scalar K (vec K) := sorry
/-⟨
smul_vec K,
⟩-/

/-
/-- Typeclass for multiplicative actions by monoids. This generalizes group actions. -/
@[protect_proj] class mul_action (α : Type u) (β : Type v) [monoid α] extends has_scalar α β :=
(one_smul : ∀ b : β, (1 : α) • b = b)
(mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b)
-/
--lemma one_smul_vec : ∀ b : vec K, (1 : K) • b = b := sorry
/-begin
    intros,
    cases b,
    ext,
    exact one_mul _,
    exact one_mul _
end-/
--lemma mul_smul_vec : ∀ (x y : K) (b : vec K), (x * y) • b = x • y • b := sorry
/-begin
    intros,
    cases b,
    ext,
    exact mul_assoc x y _,
    exact mul_assoc x y _
end-/
--instance mul_action_vec : mul_action K (vec K) := 
/-⟨
one_smul_vec K,
mul_smul_vec K,
⟩ -/

/-
class distrib_mul_action (α : Type u) (β : Type v) [monoid α] [add_monoid β]
  extends mul_action α β :=
(smul_add : ∀(r : α) (x y : β), r • (x + y) = r • x + r • y)
(smul_zero : ∀(r : α), r • (0 : β) = 0)
-/
--lemma smul_add_vec : ∀ (r : K) (x y : vec K), r • (x + y) = r • x + r • y := sorry
/-begin
    
  intros,
  ext,
  exact left_distrib _ _ _,
  exact left_distrib _ _ _
end-/
--lemma smul_zero_vec : ∀ (r : K), r • (0 : vec K) = 0 := sorry
/-begin
    intros, ext, exact mul_zero _, exact mul_zero _
end-/
--instance distrib_mul_action_K_vecK : distrib_mul_action K (vec K) := sorry
/-⟨
smul_add_vec K,
smul_zero_vec K,
⟩ -/

/- 
class semimodule (R : Type u) (M : Type v) [semiring R]
  [add_comm_monoid M] extends distrib_mul_action R M :=
(add_smul : ∀(r s : R) (x : M), (r + s) • x = r • x + s • x)
(zero_smul : ∀x : M, (0 : R) • x = 0)
-/
--lemma add_smul_vec : ∀ (r s : K) (x : vec K), (r + s) • x = r • x + s • x := sorry
/-begin
  intros,
  ext,
  exact right_distrib _ _ _,
  exact right_distrib _ _ _

end-/
--lemma zero_smul_vec : ∀ (x : vec K), (0 : K) • x = 0 := sorry
/-begin
    intros,
    ext,
    exact zero_mul _, exact zero_mul _
end-/

--def module_pf_val : module K (vec K) := sorry

--instance semimodule_K_vecK : module K (vec K) := sorry
/-⟨ 
    add_smul_vec K, 
    zero_smul_vec K 
⟩ -/

/-
/-- An additive commutative group is an additive group with commutative `(+)`. -/
@[protect_proj, ancestor add_group add_comm_monoid]
class add_comm_group (G : Type u) extends add_group G, add_comm_monoid G
-/
--instance add_comm_group_vec : add_comm_group (vec K) := sorry
/-⟨
-- add_group
    add_vec_vec K, add_assoc_vec K, vec_zero K, zero_add_vec K, add_zero_vec K, -- add_monoid
    neg_vec K,                                                                  -- has_neg
    sub_vec_vec K,                                                              -- has_sub
    sub_eq_add_neg_vec K, 
    add_left_neg_vec K,
-- commutativity
    add_comm_vec K,
⟩-/

/-
vector_space : 
  Π (R : Type u_1)                -- ring of scalars
    (M : Type u_2)                -- set of vectors
    [_inst_1 : field R]           -- implicit
    [_inst_2 : add_comm_group M], -- implicit
  Type (max u_1 u_2) :=
    semimodule R M      -- a vector space R M is a semimodule R M
-/
--instance : module K (vec K) := semimodule_K_vecK K 






/-
    ********************
    *** Affine space ***
    ********************
-/

/-
1-D Affine space operations
-/
-- ANDREW TO DR. SULLIVAN : I HAD TO CHANGE THIS DEFINITION FROM p2 - p1 TO p1 - p2
@[simp]
def sub_pt_pt (p1 p2 : pt K) : vec K := mk_vec' K (p1.to_prod - p2.to_prod) begin 
    cases p1, cases p2,

    simp *,
end
@[simp]
def add_pt_vec (p : pt K) (v : vec K) : pt K := mk_pt' K (p.to_prod + v.to_prod) begin
    cases p,
    cases v,
    simp *
end
@[simp]
def add_vec_pt (v : vec K) (p : pt K) : pt K := mk_pt' K (p.to_prod + v.to_prod) begin
    cases v,
    cases p,
    simp *
end
-- add affine combination operation here 



/-
has_vadd (vector point addition)
-/
@[simp]
def aff_vec_group_action : vec K → pt K → pt K := add_vec_pt K
instance : has_vadd (vec K) (pt K) := ⟨aff_vec_group_action K⟩


/-
class add_action (G : Type*) (P : Type*) [add_monoid G] extends has_vadd G P :=
(zero_vadd' : ∀ p : P, (0 : G) +ᵥ p = p)
(vadd_assoc' : ∀ (g1 g2 : G) (p : P), g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p)
-/
--lemma zero_vec_vadd'_a1 : ∀ p : pt K, (0 : vec K) +ᵥ p = p := 
/-begin
    intros,
    ext,--exact zero_add _,
    exact add_zero _,
    exact add_zero _
end-/
--lemma vec_add_assoc'_a1 : ∀ (g1 g2 : vec K) (p : pt K), g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p := sorry
/-begin
    intros,
    ext,
    repeat {
    cases g1,
    cases g2,
    cases p,
    cases g1__to_prod,
    cases g2__to_prod,
    cases p__to_prod,
    dsimp [has_vadd.vadd, aff_vec_group_action, add_vec_pt, mk_pt'],
    simp *,
    dsimp [has_add.add, add_vec_vec, mk_vec'],
    cc,
    }
end-/

--instance vec_add_action: add_action (vec K) (pt K) := sorry--⟨ aff_vec_group_action K, zero_vec_vadd'_a1 K, vec_add_assoc'_a1 K ⟩ 

/-
class has_vsub (G : out_param Type*) (P : Type*) :=
(vsub : P → P → G)
-/
@[simp]
def aff_pt_group_sub : pt K → pt K → vec K := sub_pt_pt K
instance pt_has_vsub : has_vsub (vec K) (pt K) := ⟨ aff_pt_group_sub K ⟩ 

--instance : nonempty (pt K) := ⟨mk_pt K 0⟩

/-
/-- An `add_torsor G P` gives a structure to the nonempty type `P`,
acted on by an `add_group G` with a transitive and free action given
by the `+ᵥ` operation and a corresponding subtraction given by the
`-ᵥ` operation. In the case of a vector space, it is an affine
space. -/
class add_torsor (G : out_param Type*) (P : Type*) [out_param $ add_group G]
  extends add_action G P, has_vsub G P :=
[nonempty : nonempty P]
(vsub_vadd' : ∀ (p1 p2 : P), (p1 -ᵥ p2 : G) +ᵥ p2 = p1)
(vadd_vsub' : ∀ (g : G) (p : P), g +ᵥ p -ᵥ p = g)
-/

--lemma pt_vsub_vadd_a1 : ∀ (p1 p2 : (pt K)), (p1 -ᵥ p2) +ᵥ p2 = p1 := sorry
/-begin
    intros,
    ext,
    --exact sub_add_cancel _ _ _,

    cases p1,
    cases p2,
    cases p1__to_prod,
    cases p2__to_prod,
    dsimp [has_vadd.vadd, aff_vec_group_action, add_vec_pt, mk_pt'],
    dsimp [has_vsub.vsub, aff_pt_group_sub, sub_pt_pt, mk_vec'],
    dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add],
    simp * at p2_inv,
    simp * at p1_inv,
    have h1 : p2__to_prod_fst = 1 := by exact p2_inv,
    have h2 : p1__to_prod_fst = 1 := by exact p1_inv,
    simp *,
    have h3 : field.sub (1:K) 1 = 0 := sub_self _,
    simp *,
    exact add_zero _,
    

    cases p1,
    cases p2,
    cases p1__to_prod,
    cases p2__to_prod,
    dsimp [has_vadd.vadd, aff_vec_group_action, add_vec_pt, mk_pt'],
    dsimp [has_vsub.vsub, aff_pt_group_sub, sub_pt_pt, mk_vec'],
    dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add],
    
    have h4:= sub_add_cancel  p1__to_prod_snd p2__to_prod_snd,
    dsimp [has_add.add, add_vec_vec, mk_vec', add_semigroup.add, add_monoid.add, sub_neg_monoid.add, add_group.add, add_comm_group.add, distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add] at h4,
    have h5 := add_comm_group.add_comm (field.sub p1__to_prod_snd p2__to_prod_snd) p2__to_prod_snd,
    dsimp [has_add.add, add_vec_vec, mk_vec', add_semigroup.add, add_monoid.add, sub_neg_monoid.add, add_group.add, add_comm_group.add, distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add] at h5,
    simp [h5] at h4,
    exact h4
    
end-/
/-
lemma pt_vadd_vsub_a1 : ∀ (g : vec K) (p : pt K), g +ᵥ p -ᵥ p = g := begin
    intros,
    ext,


    cases g,
    cases p,
    cases g__to_prod,
    cases p__to_prod,
    dsimp [has_vadd.vadd, aff_vec_group_action, add_vec_pt, mk_pt'],
    dsimp [has_vsub.vsub, aff_pt_group_sub, sub_pt_pt, mk_vec'],
    dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add],
    simp * at g_inv,
    simp * at p_inv,
    have h1 : g__to_prod_fst = 0 := by exact g_inv,
    have h2 : p__to_prod_fst = 1 := by exact p_inv,
    simp *,
    have h3 : field.add (1:K) 0 = 1 := add_zero _,
    simp *,
    exact sub_self _,

    cases g,
    cases p,
    cases g__to_prod,
    cases p__to_prod,
    dsimp [has_vadd.vadd, aff_vec_group_action, add_vec_pt, mk_pt'],
    dsimp [has_vsub.vsub, aff_pt_group_sub, sub_pt_pt, mk_vec'],
    dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add],
    
    have h4:= add_sub_cancel  g__to_prod_snd p__to_prod_snd,
    dsimp [has_add.add, add_vec_vec, mk_vec', add_semigroup.add, add_monoid.add, sub_neg_monoid.add, add_group.add, add_comm_group.add, distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add] at h4,

    cc
end
-/
--instance aff_pt_torsor : add_torsor (vec K) (pt K) := sorry
/-⟨ 
    aff_vec_group_action K,
    zero_vec_vadd'_a1 K,    -- add_action
    vec_add_assoc'_a1 K,   -- add_action
    aff_pt_group_sub K,    -- has_vsub
    pt_vsub_vadd_a1 K,     -- add_torsor
    pt_vadd_vsub_a1 K,     -- add_torsor
⟩-/

/-
Affine 1 K space
-/
open_locale affine
--instance tester : affine_space (vec K) (pt K) := sorry--aff_pt_torsor K
--instance : affine_space (vec K) (pt K) := sorry--aff_pt_torsor K

----variables (b : module K (vec K)) (a : affine_space (vec K) (pt K))


--def ttf [affine_space (vec K) (pt K)] : _ := @affine_equiv K K (pt K) 
--#check @affine_equiv K (pt K) (pt K) (vec K) (vec K) _ _ ()

instance : has_neg (vec K) := ⟨neg_vec K⟩

@[simp]
def nsmul_vec : ℕ → (vec K) → (vec K) 
| nat.zero v := vec_zero K
--| 1 v := v
| (nat.succ n) v := (add_vec_vec _) v (nsmul_vec n v)

@[simp]
def gsmul_vec : ℤ → (vec K) → (vec K) 
| (int.of_nat i) v := nsmul_vec K i v
| (int.neg_succ_of_nat i) v := (-(nsmul_vec K i v))

lemma  t : auto_param (∀ (a : vec K), gsmul_vec K 0 a = 0) (name.mk_string "try_refl_tac" name.anonymous) :=
begin
    simp [auto_param],
    intros,
    ext,
    let h0 : (gsmul_vec K 0 a) = 0 := rfl,
    simp *,
    let h0 : (gsmul_vec K 0 a) = 0 := rfl,
    simp *,
end

instance : has_add (vec K) := ⟨add_vec_vec K⟩
/-
lemma t2 : auto_param (∀ (n : ℕ) (a : vec K), gsmul_vec K (int.of_nat n.succ) a = a + gsmul_vec K (int.of_nat n) a) (name.mk_string "try_refl_tac" name.anonymous) :=
begin
    simp [auto_param],
    intros,
    cases n,
    simp *,
    ext,
    let h0 : (gsmul_vec K 1 a) = a := rfl,
    let h1 : gsmul_vec K 0 a = 0 := rfl,
    let h2 : a + 0 = a := begin
        intros,
        ext,
        dsimp [has_add.add,distrib.add, ring.add, division_ring.add, 
            field.add, add_vec_vec K, has_zero.zero, mul_zero_class.zero, mul_zero_one_class.zero,
            monoid_with_zero.zero, semiring.zero, ring.zero, division_ring.zero, field.zero],
        let h3 : field.add a.to_prod.fst field.zero = a.to_prod.fst := by simp *,

    end,
    rw [h0,h1],
    
    --induction (↑n + 1),
    let i := (↑n + 1),
    let h0 : i=(↑n + 1) := rfl,
    rw ←h0,    
    cases (↑n + 1),

    --ext,
    --unfold (gsmul_vec),
    simp *, --[gsmul_vec K],
    simp *,
end
-/
instance : add_comm_monoid (vec K) :=
⟨
    add_vec_vec K,
    begin
        intros,
        dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, division_ring.add, field.add],
        cases a,
        cases b,
        cases c,
        simp *,
        cc
    end,
    vec_zero K,
    begin
        intros,

        ext,
        exact zero_add _,
        exact zero_add _,
    end,
    begin
        intros,

        ext,
        exact add_zero _,
        exact add_zero _,

    end,
    nsmul_vec K,
    begin
        simp [auto_param],
        dsimp [0, vec_zero K],
        ext,
        cc,
        dsimp [0, vec_zero K],
        cc,
        

    end,
    begin
        simp [auto_param],
        intros,
        ext,
        simp *,
        cc,
        simp *,
        cc,
    end,
    begin
        intros,
        ext,
        exact add_comm _ _,
        exact add_comm _ _,
    end,
⟩

instance : add_monoid (vec K) := 
⟨
add_vec_vec K,
begin
    intros,
    dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, division_ring.add, field.add],
    cases a,
    cases b,
    cases c,
    simp *,
    cc
end,
vec_zero K,
begin
    intros,

    ext,
    exact zero_add _,
    exact zero_add _,
end,
begin
    intros,

    ext,
    exact add_zero _,
    exact add_zero _,

end,
nsmul_vec K
⟩

instance : sub_neg_monoid (vec K) := {
--..(show add_monoid (vec K), by apply_instance),
neg := (neg_vec K),
..(show add_monoid (vec K), by apply_instance),

}

instance : add_group (vec K) := {
add_left_neg := begin
    intros,
    let h0 : (-a + a).to_prod = (-a).to_prod + a.to_prod := rfl,
    let h1 : (0 : vec K).to_prod.fst = 0 := rfl,
    let h2 : (-a).to_prod = -a.to_prod := begin
        --cases a,
        ext,
        simp *,
        let h3 : a.to_prod.fst = 0 := by exact a.inv,
        let h4 : (-a.to_prod.fst) = 0 := begin
            rw h3,
            exact neg_zero,
        end, 
        rw h4,
        exact (-a).inv,
        cases a,
        simp *,
        dsimp [has_neg.neg, sub_neg_monoid.neg, add_group.neg],
        let h5 : add_comm_group.neg 1 * a__to_prod.snd = -a__to_prod.snd := by exact neg_one_mul _,
        simp [h5],
        trivial
    end,

    ext,
    rw [h0],
    rw h1,
    rw h2,
    simp *,
    rw [h0],
    rw h2,
    simp *,
    let h6 : (0 : vec K).to_prod.snd = 0 := rfl,
    simp *,
end,
..(show sub_neg_monoid (vec K), by apply_instance),
}

/-#check ({
..(show )

}




: affine_space (vec K) (pt K))
-/
--def 

--: add_comm_monoid (vec K))
instance : add_comm_group (vec K) :={
    add_comm := begin
        intros,
        ext,
        exact add_comm _ _,
        exact add_comm _ _,
    end,
--to_add_group := (show add_group (vec K), by apply_instance),
--to_add_comm_monoid := (show add_comm_monoid (vec K), by apply_instance),
..(show add_group (vec K), by apply_instance)
}
/-
#check (
⟨
add_vec_vec K,
begin
    intros,
    dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, division_ring.add, field.add],
    cases a,
    cases b,
    cases c,
    simp *,
    cc
end,
vec_zero K,
begin
    intros,

    ext,
    exact zero_add _,
    exact zero_add _,
end,
begin
    intros,

    ext,
    exact add_zero _,
    exact add_zero _,

end,
nsmul_vec K,
begin
    simp [auto_param],
    dsimp [0, vec_zero K],
    ext,
    cc,
    dsimp [0, vec_zero K],
    cc,
    

end,
begin
    simp [auto_param],
    intros,
    ext,
    simp *,
    cc,
    simp *,
    cc,
end,
neg_vec K,
sub_vec_vec K,
begin
    simp [auto_param],
    intros,
    ext,
    cc,
    cc,
end,
gsmul_vec K,
begin
    simp [auto_param],
    intros,
    ext,
    let h0 : (gsmul_vec K 0 a) = 0 := rfl,
    simp *,
    let h0 : (gsmul_vec K 0 a) = 0 := rfl,
    simp *,
end,
begin

    simp [auto_param],
    intros,
    cases n,
    simp *,
    ext,
    let h0 : (gsmul_vec K 1 a) = a := rfl,
    let h1 : gsmul_vec K 0 a = 0 := rfl,
    let h2 : a + 0 = a := by cc,begin
        intros,
        ext,
        dsimp [has_add.add,distrib.add, ring.add, division_ring.add, 
            field.add, add_vec_vec K, has_zero.zero, mul_zero_class.zero, mul_zero_one_class.zero,
            monoid_with_zero.zero, semiring.zero, ring.zero, division_ring.zero, field.zero],
        let h3 : field.add a.to_prod.fst field.zero = a.to_prod.fst := by simp *,

    end,
    rw [h0,h1],
    simp *,
    
    --induction (↑n + 1),
    let i := (↑n + 1),
    let h0 : i=(↑n + 1) := rfl,
    rw ←h0,    
    cases (↑n + 1),
end,
⟩ : add_comm_group (vec K) )
-/

instance : has_scalar K (vec K) := ⟨ smul_vec K ⟩

lemma ma1 : ∀b : vec K, 1 • b = b := sorry

instance : mul_action K (vec K) := 
⟨
begin
    intros,
    cases b,
    ext,
    exact one_mul _,
    exact one_mul _
end, 
begin
    intros,
    cases b,
    ext,
    exact mul_assoc x y _,
    exact mul_assoc x y _
end,
⟩

lemma ma2 : ∀ (r : K) (x y : vec K), r • (x + y) = r • x + r • y := begin
intros,
        ext,
        exact left_distrib _ _ _,
        exact left_distrib _ _ _
end

instance : distrib_mul_action K (vec K) := 
⟨
    begin
        exact ma2 K,
        /-intros,
        ext,
        exact left_distrib _ _ _,
        exact left_distrib _ _ _
-/
    end, 
    begin
    intros, ext, exact mul_zero _, exact mul_zero _
    end
⟩

lemma ma3 : ∀ (r s : K) (x : vec K), (r + s) • x = r • x + s • x := begin
  intros,
  ext,
  exact right_distrib _ _ _,
  exact right_distrib _ _ _


end

instance a2 : module K (vec K) := ⟨
begin
    exact ma3 K
end,
begin
    intros,
    ext,
    exact zero_mul _, exact zero_mul _
end
⟩

lemma ma5 : ∀ (p1 p2 : pt K), p1 -ᵥ p2 +ᵥ p2 = p1 := 
begin
intros,
    ext,
    --exact sub_add_cancel _ _ _,

    cases p1,
    cases p2,
    cases p1__to_prod,
    cases p2__to_prod,
    dsimp [has_vadd.vadd, aff_vec_group_action, add_vec_pt, mk_pt'],
    dsimp [has_vsub.vsub, aff_pt_group_sub, sub_pt_pt, mk_vec'],
    dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add],
    simp * at p2_inv,
    simp * at p1_inv,
    have h1 : p2__to_prod_fst = 1 := by exact p2_inv,
    have h2 : p1__to_prod_fst = 1 := by exact p1_inv,
    simp *,
    have h3 : field.sub (1:K) 1 = 0 := sub_self _,
    simp *,
    exact add_zero _,
    

    cases p1,
    cases p2,
    cases p1__to_prod,
    cases p2__to_prod,
    dsimp [has_vadd.vadd, aff_vec_group_action, add_vec_pt, mk_pt'],
    dsimp [has_vsub.vsub, aff_pt_group_sub, sub_pt_pt, mk_vec'],
    dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add],
    
    have h4:= sub_add_cancel  p1__to_prod_snd p2__to_prod_snd,
    dsimp [has_add.add, add_zero_class.add, add_vec_vec, mk_vec', add_semigroup.add, add_monoid.add, sub_neg_monoid.add, add_group.add, add_comm_group.add, distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add] at h4,
    have h5 := add_comm_group.add_comm (field.sub p1__to_prod_snd p2__to_prod_snd) p2__to_prod_snd,
    dsimp [has_add.add, add_vec_vec, mk_vec', add_semigroup.add, add_monoid.add, sub_neg_monoid.add, add_group.add, add_comm_group.add, distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add] at h5,

  --  have h6 := add_sub_cancel
    simp [h5] at h4,
    exact h4,
end
lemma zero_vec_vadd'_a1 : ∀ p : pt K, (0 : vec K) +ᵥ p = p := 
begin
    intros,
    ext,--exact zero_add _,
    exact add_zero _,
    exact add_zero _
end

instance : add_action (vec K) (pt K) :=
⟨
begin
    exact zero_vec_vadd'_a1 K
end,
begin
    intros,
    ext,
    cases g₁,
    cases g₂,
    cases p,
    cases g₁__to_prod,
    cases g₂__to_prod,
    cases p__to_prod,
    dsimp [has_vadd.vadd, aff_vec_group_action, add_vec_pt, mk_pt'],
    --simp *,
    dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, add_zero_class.add, distrib.add, add_monoid.add, ring.add, division_ring.add],
    cc,
    
    cases g₁,
    cases g₂,
    cases p,
    cases g₁__to_prod,
    cases g₂__to_prod,
    cases p__to_prod,
    dsimp [has_vadd.vadd, aff_vec_group_action, add_vec_pt, mk_pt'],
    --simp *,
    dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, add_zero_class.add, distrib.add, add_monoid.add, ring.add, division_ring.add],
    cc,
    --repeat not working?

end
⟩

instance : nonempty (pt K) := ⟨mk_pt K 1⟩
/-
@[protect_proj] class add_action (G : Type*) (P : Type*) [add_monoid G] extends has_vadd G P :=
(zero_vadd : ∀ p : P, (0 : G) +ᵥ p = p)
(add_vadd : ∀ (g₁ g₂ : G) (p : P), (g₁ + g₂) +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p))
-/

instance a3 : affine_space (vec K) (pt K) := ⟨
    ma5 K,
    begin
        intros,
        ext,


        cases g,
        cases p,
        cases g__to_prod,
        cases p__to_prod,
        dsimp [has_vadd.vadd, aff_vec_group_action, add_vec_pt, mk_pt'],
        dsimp [has_vsub.vsub, aff_pt_group_sub, sub_pt_pt, mk_vec'],
        dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add],
        simp * at g_inv,
        simp * at p_inv,
        have h1 : g__to_prod_fst = 0 := by exact g_inv,
        have h2 : p__to_prod_fst = 1 := by exact p_inv,
        simp *,
        have h3 : field.add (1:K) 0 = 1 := add_zero _,
        simp *,
        exact sub_self _,

        cases g,
        cases p,
        cases g__to_prod,
        cases p__to_prod,
        dsimp [has_vadd.vadd, aff_vec_group_action, add_vec_pt, mk_pt'],
        dsimp [has_vsub.vsub, aff_pt_group_sub, sub_pt_pt, mk_vec'],
        dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add],
        
        have h4:= add_sub_cancel  g__to_prod_snd p__to_prod_snd,
        dsimp [has_add.add, add_vec_vec, mk_vec', add_semigroup.add, add_monoid.add, sub_neg_monoid.add, add_group.add, add_comm_group.add, distrib.add, ring.add, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub, division_ring.add] at h4,

        cc
    end,
⟩


#check (pt K) ≃ᵃ[K] (pt K) --works!