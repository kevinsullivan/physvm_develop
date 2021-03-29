import linear_algebra.affine_space.basic
import ...math.aff1Kcoord.aff1Kcoord_std

open_locale affine

/-
Framed points, vectors, frames
-/
namespace geom

universes u --v w
variables 
{K : Type u} [field K] [inhabited K] 

/-
Add frames and (coordinate) spaces based on frames
-/

structure position {f : fm K} (s : spc K f ) extends point s 
def mk_position' {f : fm K} (s : spc K f ) (p : point s) : position s := position.mk p  
def mk_position {f : fm K} (s : spc K f ) (k : K) : position s := position.mk (mk_point s k) 

structure translation {f : fm K} (s : spc K f ) extends vectr s 
def mk_translation' {f : fm K} (s : spc K f ) (v : vectr s) : translation s := translation.mk v
def mk_translation  {f : fm K} (s : spc K f ) (k : K) : translation s := translation.mk (mk_vectr s k) 

-- note that we don't extend fm
def mk_geom_frame {parent : fm K} {s : spc K parent} (p : position s) (v : translation s) :=
fm.deriv (p.to_point.to_pt, v.to_vectr.to_vec) parent   -- TODO: make sure v ≠ 0


/-
    *************************************
    Instantiate vector_space K (translation K)
    *************************************
-/

variables {f : fm K} {s : spc K f } 

def add_vectr_vectr (v1 v2 : translation s) : translation s := 
    mk_duration' s (v1.to_vectr + v2.to_vectr)
def smul_vectr (k : K) (v : translation s) : translation s := 
    mk_duration' s (k • v.to_vectr)
def neg_vectr (v : translation s) : translation s := 
    mk_duration' s ((-1 : K) • v.to_vectr)
def sub_vectr_vectr (v1 v2 : translation s) : translation s :=    -- v1-v2
    add_vectr_vectr v1 (neg_vectr v2)

-- See unframed file for template for proving vector_space

instance has_add_vectr : has_add (translation s) := ⟨ add_vectr_vectr ⟩
lemma add_assoc_vectr : ∀ a b c : translation s, a + b + c = a + (b + c) := sorry
instance add_semigroup_vectr : add_semigroup (translation s) := ⟨ add_vectr_vectr, add_assoc_vectr ⟩ 

def vectr_zero  := mk_duration s 0
instance has_zero_vectr : has_zero (translation s) := ⟨vectr_zero⟩

lemma zero_add_vectr : ∀ a : translation s, 0 + a = a := sorry
lemma add_zero_vectr : ∀ a : translation s, a + 0 = a := sorry
instance add_monoid_vectr : add_monoid (translation s) := ⟨ 
    -- add_semigroup
    add_vectr_vectr, 
    add_assoc_vectr, 
    -- has_zero
    vectr_zero,
    -- new structure 
    zero_add_vectr, 
    add_zero_vectr
⟩

instance has_neg_vectr : has_neg (translation s) := ⟨neg_vectr⟩
instance has_sub_vectr : has_sub (translation s) := ⟨ sub_vectr_vectr ⟩ 
lemma sub_eq_add_neg_vectr : ∀ a b : translation s, a - b = a + -b := sorry
instance sub_neg_monoid_vectr : sub_neg_monoid (translation s) := ⟨ 
    add_vectr_vectr, add_assoc_vectr, vectr_zero, zero_add_vectr, add_zero_vectr, -- add_monoid
    neg_vectr,                                                                  -- has_neg
    sub_vectr_vectr,                                                              -- has_sub
    sub_eq_add_neg_vectr,                                                       -- new
⟩ 

lemma add_left_neg_vectr : ∀ a : translation s, -a + a = 0 := sorry
instance : add_group (translation s) := ⟨
    -- sub_neg_monoid
    add_vectr_vectr, add_assoc_vectr, vectr_zero, zero_add_vectr, add_zero_vectr, -- add_monoid
    neg_vectr,                                                                  -- has_neg
    sub_vectr_vectr,                                                              -- has_sub
    sub_eq_add_neg_vectr, 
    -- new
    add_left_neg_vectr,
⟩ 

lemma add_comm_vectr : ∀ a b : translation s, a + b = b + a := sorry
instance add_comm_semigroup_vectr : add_comm_semigroup (translation s) := ⟨
    -- add_semigroup
    add_vectr_vectr, 
    add_assoc_vectr,
    add_comm_vectr,
⟩

instance add_comm_monoid_vectr : add_comm_monoid (translation s) := ⟨
-- add_monoid
    -- add_semigroup
    add_vectr_vectr, 
    add_assoc_vectr, 
    -- has_zero
    vectr_zero,
    -- new structure 
    zero_add_vectr, 
    add_zero_vectr,
-- add_comm_semigroup (minus repeats)
    add_comm_vectr,
⟩

instance has_scalar_vectr : has_scalar K (translation s) := ⟨
smul_vectr,
⟩

lemma one_smul_vectr : ∀ b : translation s, (1 : K) • b = b := sorry
lemma mul_smul_vectr : ∀ (x y : K) (b : translation s), (x * y) • b = x • y • b := sorry
instance mul_action_vectr : mul_action K (translation s) := ⟨
one_smul_vectr,
mul_smul_vectr,
⟩ 

lemma smul_add_vectr : ∀(r : K) (x y : translation s), r • (x + y) = r • x + r • y := sorry
lemma smul_zero_vectr : ∀(r : K), r • (0 : translation s) = 0 := sorry
instance distrib_mul_action_K_vectrKx : distrib_mul_action K (translation s) := ⟨
smul_add_vectr,
smul_zero_vectr,
⟩ 

-- renaming vs template due to clash with name "s" for prevailing variable
lemma add_smul_vectr : ∀ (a b : K) (x : translation s), (a + b) • x = a • x + b • x := sorry
lemma zero_smul_vectr : ∀ (x : translation s), (0 : K) • x = 0 := sorry
instance semimodule_K_durationK : semimodule K (translation s) := ⟨ add_smul_vectr, zero_smul_vectr ⟩ 

instance add_comm_group_vectr : add_comm_group (translation s) := ⟨
-- add_group
    add_vectr_vectr, add_assoc_vectr, vectr_zero, zero_add_vectr, add_zero_vectr, -- add_monoid
    neg_vectr,                                                                  -- has_neg
    sub_vectr_vectr,                                                              -- has_sub
    sub_eq_add_neg_vectr, 
    add_left_neg_vectr,
-- commutativity
    add_comm_vectr,
⟩

/-
upshot : inherited vector space properties, with overloaded operations and notations
-/

instance : vector_space K (translation s) := @geom.semimodule_K_durationK K _ _ f s


/-
    ********************
    *** Affine space ***
    ********************
-/


/-
Affine operations
-/
instance : has_add (translation s) := ⟨add_vectr_vectr⟩
instance : has_zero (translation s) := ⟨vectr_zero⟩
instance : has_neg (translation s) := ⟨neg_vectr⟩

/-
Lemmas needed to implement affine space API
-/

def sub_point_point {f : fm K} {s : spc K f } (p1 p2 : position s) : translation s := 
    mk_duration' s (p2.to_point -ᵥ p1.to_point)
def add_point_vectr {f : fm K} {s : spc K f } (p : position s) (v : translation s) : position s := 
    mk_position' s (v.to_vectr +ᵥ p.to_point) -- reorder assumes order is irrelevant
def add_vectr_point {f : fm K} {s : spc K f } (v : translation s) (p : position s) : position s := 
    mk_position' s (v.to_vectr +ᵥ p.to_point)

def aff_vectr_group_action : translation s → position s → position s := add_vectr_point
instance : has_vadd (translation s) (position s) := ⟨aff_vectr_group_action⟩

lemma zero_vectr_vadd'_a1 : ∀ p : position s, (0 : translation s) +ᵥ p = p := sorry
lemma vectr_add_assoc'_a1 : ∀ (g1 g2 : translation s) (p : position s), g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p := sorry
instance vectr_add_action: add_action (translation s) (position s) := 
⟨ aff_vectr_group_action, zero_vectr_vadd'_a1, vectr_add_assoc'_a1 ⟩ 

def aff_point_group_sub : position s → position s → translation s := sub_point_point
instance point_has_vsub : has_vsub (translation s) (position s) := ⟨ aff_point_group_sub ⟩ 

instance : nonempty (position s) := ⟨mk_position s 0⟩

lemma point_vsub_vadd_a1 : ∀ (p1 p2 : (position s)), (p1 -ᵥ p2) +ᵥ p2 = p1 := sorry
lemma point_vadd_vsub_a1 : ∀ (g : translation s) (p : position s), g +ᵥ p -ᵥ p = g := sorry
instance aff_point_torsor : add_torsor (translation s) (position s) := 
⟨ 
    aff_vectr_group_action,
    zero_vectr_vadd'_a1,    -- add_action
    vectr_add_assoc'_a1,   -- add_action
    aff_point_group_sub,    -- has_vsub
    point_vsub_vadd_a1,     -- add_torsor
    point_vadd_vsub_a1,     -- add_torsor
⟩

open_locale affine

/-
upshot : inherited affine space properties with overloaded operations and notations
-/
instance : affine_space (translation s) (position s) := @geom.aff_point_torsor K _ _ f s

end geom