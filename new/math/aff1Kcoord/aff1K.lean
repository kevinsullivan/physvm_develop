import linear_algebra.affine_space.basic
import ..lin2Kcoord.lin2kcoord


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

-- 1-D affine K jects obrep by 2-D linear K vectors

structure pt extends K × K := (inv : fst = 1)
def mk_pt' (p : K × K) (i : p.1 = 1): pt K := @pt.mk K _ _ p i    -- private
def mk_pt (k : K) : pt K  := @pt.mk K _ _ (1, k) rfl              -- exported

structure vec extends K × K := (inv : fst = 0)
def mk_vec' (p : K × K) (i : p.1 = 0): vec K := @vec.mk K _ _ p i -- private
def mk_vec (k : K) : vec K := @vec.mk K _ _ (0, k) rfl            -- exported


/-
    ********************
    *** Vector space ***
    ********************
-/


def add_vec_vec (v1 v2 : vec K) : vec K := mk_vec' K (v1.to_prod + v2.to_prod) sorry
def smul_vec (k : K) (v : vec K) : vec K := mk_vec' K (k • v.to_prod) sorry --smul
def neg_vec (v : vec K) : vec K := mk_vec' K ((-1 : K) • v.to_prod) sorry
def sub_vec_vec (v2 v1 : vec K) : vec K := add_vec_vec K v2 (neg_vec K v1)  -- v2-v1

/-
class add_semigroup (G : Type u) extends has_add G :=
(add_assoc : ∀ a b c : G, a + b + c = a + (b + c))
-/
instance has_add_vec : has_add (vec K) := ⟨ add_vec_vec K ⟩
lemma add_assoc_vec : ∀ a b c : vec K, a + b + c = a + (b + c) := sorry
instance add_semigroup_vec : add_semigroup (vec K) := ⟨ add_vec_vec K, add_assoc_vec K ⟩ 

/-
has_zero vec
-/
def vec_zero  := mk_vec K 0
instance has_zero_vec : has_zero (vec K) := ⟨vec_zero K⟩

/-
class add_monoid (M : Type u) extends add_semigroup M, has_zero M :=
(zero_add : ∀ a : M, 0 + a = a) (add_zero : ∀ a : M, a + 0 = a)
-/
lemma zero_add_vec : ∀ a : vec K, 0 + a = a := sorry
lemma add_zero_vec : ∀ a : vec K, a + 0 = a := sorry
instance add_monoid_vec : add_monoid (vec K) := ⟨ 
    -- add_semigroup
    add_vec_vec K, 
    add_assoc_vec K, 
    -- has_zero
    vec_zero K,
    -- new structure 
    zero_add_vec K, 
    add_zero_vec K
⟩


/-
sub_neg_monoid (G : Type u) extends add_monoid G, has_neg G, has_sub G :=
(sub := λ a b, a + -b)
(sub_eq_add_neg : ∀ a b : G, a - b = a + -b . try_refl_tac)
-/
instance has_neg_vec : has_neg (vec K) := ⟨neg_vec K⟩
instance has_sub_vec : has_sub (vec K) := ⟨ sub_vec_vec K ⟩ 
lemma sub_eq_add_neg_vec : ∀ a b : vec K, a - b = a + -b := sorry
instance sub_neg_monoid_vec : sub_neg_monoid (vec K) := ⟨ 
    add_vec_vec K, add_assoc_vec K, vec_zero K, zero_add_vec K, add_zero_vec K, -- add_monoid
    neg_vec K,                                                                  -- has_neg
    sub_vec_vec K,                                                              -- has_sub
    sub_eq_add_neg_vec K,                                                       -- new
⟩ 


/-
class add_group (A : Type u) extends sub_neg_monoid A :=
(add_left_neg : ∀ a : A, -a + a = 0)
-/
lemma add_left_neg_vec : ∀ a : vec K, -a + a = 0 := sorry
instance : add_group (vec K) := ⟨
    -- sub_neg_monoid
    add_vec_vec K, add_assoc_vec K, vec_zero K, zero_add_vec K, add_zero_vec K, -- add_monoid
    neg_vec K,                                                                  -- has_neg
    sub_vec_vec K,                                                              -- has_sub
    sub_eq_add_neg_vec K, 
    -- new
    add_left_neg_vec K,
⟩ 

/-
Material up to now is needed for affine_space, as defined below. 
The rest of this section is needed for vector_space (vec K).
-/

/-
add_comm_semigroup (G : Type u) extends add_semigroup G :=
(add_comm : ∀ a b : G, a + b = b + a)
-/
lemma add_comm_vec : ∀ a b : vec K, a + b = b + a := sorry
instance add_comm_semigroup_vec : add_comm_semigroup (vec K) := ⟨
    -- add_semigroup
    add_vec_vec K, 
    add_assoc_vec K,
    add_comm_vec K,
⟩


/-
/-- An additive commutative monoid is an additive monoid with commutative `(+)`. -/
@[protect_proj, ancestor add_monoid add_comm_semigroup]
class add_comm_monoid (M : Type u) extends add_monoid M, add_comm_semigroup M
attribute [to_additive] comm_monoid
-/

instance add_comm_monoid_vec : add_comm_monoid (vec K) := ⟨
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
⟩

/-
/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
class has_scalar (α : Type u) (γ : Type v) := (smul : α → γ → γ)
-/
instance has_scalar_vec : has_scalar K (vec K) := ⟨
smul_vec K,
⟩

/-
/-- Typeclass for multiplicative actions by monoids. This generalizes group actions. -/
@[protect_proj] class mul_action (α : Type u) (β : Type v) [monoid α] extends has_scalar α β :=
(one_smul : ∀ b : β, (1 : α) • b = b)
(mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b)
-/
lemma one_smul_vec : ∀ b : vec K, (1 : K) • b = b := sorry
lemma mul_smul_vec : ∀ (x y : K) (b : vec K), (x * y) • b = x • y • b := sorry
instance mul_action_vec : mul_action K (vec K) := ⟨
one_smul_vec K,
mul_smul_vec K,
⟩ 

/-
class distrib_mul_action (α : Type u) (β : Type v) [monoid α] [add_monoid β]
  extends mul_action α β :=
(smul_add : ∀(r : α) (x y : β), r • (x + y) = r • x + r • y)
(smul_zero : ∀(r : α), r • (0 : β) = 0)
-/
lemma smul_add_vec : ∀ (r : K) (x y : vec K), r • (x + y) = r • x + r • y := sorry
lemma smul_zero_vec : ∀ (r : K), r • (0 : vec K) = 0 := sorry
instance distrib_mul_action_K_vecK : distrib_mul_action K (vec K) := ⟨
smul_add_vec K,
smul_zero_vec K,
⟩ 

/- 
class semimodule (R : Type u) (M : Type v) [semiring R]
  [add_comm_monoid M] extends distrib_mul_action R M :=
(add_smul : ∀(r s : R) (x : M), (r + s) • x = r • x + s • x)
(zero_smul : ∀x : M, (0 : R) • x = 0)
-/
lemma add_smul_vec : ∀ (r s : K) (x : vec K), (r + s) • x = r • x + s • x := sorry
lemma zero_smul_vec : ∀ (x : vec K), (0 : K) • x = 0 := sorry
instance semimodule_K_vecK : semimodule K (vec K) := ⟨ 
    add_smul_vec K, 
    zero_smul_vec K 
⟩ 

/-
/-- An additive commutative group is an additive group with commutative `(+)`. -/
@[protect_proj, ancestor add_group add_comm_monoid]
class add_comm_group (G : Type u) extends add_group G, add_comm_monoid G
-/
instance add_comm_group_vec : add_comm_group (vec K) := ⟨
-- add_group
    add_vec_vec K, add_assoc_vec K, vec_zero K, zero_add_vec K, add_zero_vec K, -- add_monoid
    neg_vec K,                                                                  -- has_neg
    sub_vec_vec K,                                                              -- has_sub
    sub_eq_add_neg_vec K, 
    add_left_neg_vec K,
-- commutativity
    add_comm_vec K,
⟩

/-
vector_space : 
  Π (R : Type u_1)                -- ring of scalars
    (M : Type u_2)                -- set of vectors
    [_inst_1 : field R]           -- implicit
    [_inst_2 : add_comm_group M], -- implicit
  Type (max u_1 u_2) :=
    semimodule R M      -- a vector space R M is a semimodule R M
-/
instance : vector_space K (vec K) := semimodule_K_vecK K 

/-
    ********************
    *** Affine space ***
    ********************
-/

/-
1-D Affine space operations
-/
def sub_pt_pt (p1 p2 : pt K) : vec K := mk_vec' K (p2.to_prod - p1.to_prod) sorry
def add_pt_vec (p : pt K) (v : vec K) : pt K := mk_pt' K (p.to_prod + v.to_prod) sorry
def add_vec_pt (v : vec K) (p : pt K) : pt K := mk_pt' K (p.to_prod + v.to_prod) sorry
-- add affine combination operation here 



/-
has_vadd (vector point addition)
-/
def aff_vec_group_action : vec K → pt K → pt K := add_vec_pt K
instance : has_vadd (vec K) (pt K) := ⟨aff_vec_group_action K⟩


/-
class add_action (G : Type*) (P : Type*) [add_monoid G] extends has_vadd G P :=
(zero_vadd' : ∀ p : P, (0 : G) +ᵥ p = p)
(vadd_assoc' : ∀ (g1 g2 : G) (p : P), g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p)
-/
lemma zero_vec_vadd'_a1 : ∀ p : pt K, (0 : vec K) +ᵥ p = p := sorry
lemma vec_add_assoc'_a1 : ∀ (g1 g2 : vec K) (p : pt K), g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p := sorry
instance vec_add_action: add_action (vec K) (pt K) := ⟨ aff_vec_group_action K, zero_vec_vadd'_a1 K, vec_add_assoc'_a1 K ⟩ 

/-
class has_vsub (G : out_param Type*) (P : Type*) :=
(vsub : P → P → G)
-/
def aff_pt_group_sub : pt K → pt K → vec K := sub_pt_pt K
instance pt_has_vsub : has_vsub (vec K) (pt K) := ⟨ aff_pt_group_sub K ⟩ 

instance : nonempty (pt K) := ⟨mk_pt K 0⟩

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
lemma pt_vsub_vadd_a1 : ∀ (p1 p2 : (pt K)), (p1 -ᵥ p2) +ᵥ p2 = p1 := sorry
lemma pt_vadd_vsub_a1 : ∀ (g : vec K) (p : pt K), g +ᵥ p -ᵥ p = g := sorry
instance aff_pt_torsor : add_torsor (vec K) (pt K) := 
⟨ 
    aff_vec_group_action K,
    zero_vec_vadd'_a1 K,    -- add_action
    vec_add_assoc'_a1 K,   -- add_action
    aff_pt_group_sub K,    -- has_vsub
    pt_vsub_vadd_a1 K,     -- add_torsor
    pt_vadd_vsub_a1 K,     -- add_torsor
⟩

/-
Affine 1 K space
-/
open_locale affine
instance : affine_space (vec K) (pt K) := aff_pt_torsor K

