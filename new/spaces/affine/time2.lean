import .affine1K_framed
import linear_algebra.affine_space.basic

open_locale affine

/-
Framed points, vectors, frames
-/

universes u --v w
variables 
(K : Type u) [field K] [inhabited K] 

/-
Add frames and (coordinate) spaces based on frames
-/

structure point {f : fm K} (s : spc K f ) extends pt K
def mk_point' {f : fm K} (s : spc K f ) (p : pt K) : point K s := point.mk p  
def mk_point {f : fm K} (s : spc K f ) (k : K) : point K s := point.mk (mk_pt K k)  

structure vectr {f : fm K} (s : spc K f ) extends vec K
def mk_vectr' {f : fm K} (s : spc K f ) (v : vec K) : vectr K s := vectr.mk v
def mk_vectr {f : fm K} (s : spc K f ) (k : K) : vectr K s := vectr.mk (mk_vec K k)  

-- note that we don't extend fm
def mk_frame {parent : fm K} {s : spc K parent}  (p : point K s) (v : vectr K s) :=
fm.deriv (p.to_pt, v.to_vec) parent   -- TODO: make sure v ≠ 0


/-
    *************************************
    Instantiate vector_space K (vector K)
    *************************************
-/

def add_vectr_vectr {f : fm K} {s : spc K f } (v1 v2 : vectr K s) : vectr K s := 
    mk_vectr' K s (v1.to_vec + v2.to_vec)
def smul_vectr {f : fm K} {s : spc K f } (k : K) (v : vectr K s) : vectr K s := 
    mk_vectr' K s (k • v.to_vec)
def neg_vectr {f : fm K} {s : spc K f } (v : vectr K s) : vectr K s := 
    mk_vectr' K s ((-1 : K) • v.to_vec)
def sub_vectr_vectr {f : fm K} {s : spc K f } (v1 v2 : vectr K s) : vectr K s :=    -- v1-v2
    add_vectr_vectr K v1 (neg_vectr K v2)

-- See unframed file for template for proving vector_space

instance has_add_vectr : has_add (vectr K s) := ⟨ add_vectr_vectr K ⟩
lemma add_assoc_vectr : ∀ a b c : vectr K s, a + b + c = a + (b + c) := sorry
instance add_semigroup_vectr : add_semigroup (vectr K s) := ⟨ add_vectr_vectr K, add_assoc_vectr K ⟩ 

def vectr_zero  := mk_vectr K s 0
instance has_zero_vectr : has_zero (vectr K s) := ⟨vectr_zero K⟩

lemma zero_add_vectr : ∀ a : vectr K s, 0 + a = a := sorry
lemma add_zero_vectr : ∀ a : vectr K s, a + 0 = a := sorry
instance add_monoid_vectr : add_monoid (vectr K s) := ⟨ 
    -- add_semigroup
    add_vectr_vectr K, 
    add_assoc_vectr K, 
    -- has_zero
    vectr_zero K,
    -- new structure 
    zero_add_vectr K, 
    add_zero_vectr K
⟩

instance has_neg_vectr : has_neg (vectr K s) := ⟨neg_vectr K⟩
instance has_sub_vectr : has_sub (vectr K s) := ⟨ sub_vectr_vectr K ⟩ 
lemma sub_eq_add_neg_vectr : ∀ a b : vectr K s, a - b = a + -b := sorry
instance sub_neg_monoid_vectr : sub_neg_monoid (vectr K s) := ⟨ 
    add_vectr_vectr K, add_assoc_vectr K, vectr_zero K, zero_add_vectr K, add_zero_vectr K, -- add_monoid
    neg_vectr K,                                                                  -- has_neg
    sub_vectr_vectr K,                                                              -- has_sub
    sub_eq_add_neg_vectr K,                                                       -- new
⟩ 

lemma add_left_neg_vectr : ∀ a : vectr K s, -a + a = 0 := sorry
instance : add_group (vectr K s) := ⟨
    -- sub_neg_monoid
    add_vectr_vectr K, add_assoc_vectr K, vectr_zero K, zero_add_vectr K, add_zero_vectr K, -- add_monoid
    neg_vectr K,                                                                  -- has_neg
    sub_vectr_vectr K,                                                              -- has_sub
    sub_eq_add_neg_vectr K, 
    -- new
    add_left_neg_vectr K,
⟩ 

lemma add_comm_vectr : ∀ a b : vectr K s, a + b = b + a := sorry
instance add_comm_semigroup_vectr : add_comm_semigroup (vectr K s) := ⟨
    -- add_semigroup
    add_vectr_vectr K, 
    add_assoc_vectr K,
    add_comm_vectr K,
⟩

instance add_comm_monoid_vectr : add_comm_monoid (vectr K s) := ⟨
-- add_monoid
    -- add_semigroup
    add_vectr_vectr K, 
    add_assoc_vectr K, 
    -- has_zero
    vectr_zero K,
    -- new structure 
    zero_add_vectr K, 
    add_zero_vectr K,
-- add_comm_semigroup (minus repeats)
    add_comm_vectr K,
⟩

instance has_scalar_vectr : has_scalar K (vectr K s) := ⟨
smul_vectr K,
⟩

lemma one_smul_vectr : ∀ b : vectr K s, (1 : K) • b = b := sorry
lemma mul_smul_vectr : ∀ (x y : K) (b : vectr K s), (x * y) • b = x • y • b := sorry
instance mul_action_vectr : mul_action K (vectr K s) := ⟨
one_smul_vectr K,
mul_smul_vectr K,
⟩ 

lemma smul_add_vectr : ∀(r : K) (x y : vectr K s), r • (x + y) = r • x + r • y := sorry
lemma smul_zero_vectr : ∀(r : K), r • (0 : vectr K s) = 0 := sorry
instance distrib_mul_action_K_vectrK : distrib_mul_action K (vectr K s) := ⟨
smul_add_vectr K,
smul_zero_vectr K,
⟩ 

-- renaming vs template due to clash with name "s" for prevailing variable
lemma add_smul_vectr : ∀ (a b : K) (x : vectr K s), (a + b) • x = a • x + b • x := sorry
lemma zero_smul_vectr : ∀ (x : vectr K s), (0 : K) • x = 0 := sorry
instance semimodule_K_vectrK : semimodule K (vectr K s) := ⟨ 
    add_smul_vectr K, 
    zero_smul_vectr K 
⟩ 

instance add_comm_group_vectr : add_comm_group (vectr K s) := ⟨
-- add_group
    add_vectr_vectr K, add_assoc_vectr K, vectr_zero K, zero_add_vectr K, add_zero_vectr K, -- add_monoid
    neg_vectr K,                                                                  -- has_neg
    sub_vectr_vectr K,                                                              -- has_sub
    sub_eq_add_neg_vectr K, 
    add_left_neg_vectr K,
-- commutativity
    add_comm_vectr K,
⟩

instance : vector_space K (vectr K s) := semimodule_K_vectrK K 


/-
    ********************
    *** Affine space ***
    ********************
-/


/-
Affine operations
-/
instance : has_add (vectr K s) := ⟨add_vectr_vectr K⟩
instance : has_zero (vectr K s) := ⟨vectr_zero K⟩
instance : has_neg (vectr K s) := ⟨neg_vectr K⟩

/-
Lemmas needed to implement affine space API
-/

def sub_point_point {f : fm K} {s : spc K f } (p1 p2 : point K s) : vectr K s := 
    mk_vectr' K s (p2.to_pt -ᵥ p1.to_pt)
def add_point_vectr {f : fm K} {s : spc K f } (p : point K s) (v : vectr K s) : point K s := 
    mk_point' K s (v.to_vec +ᵥ p.to_pt) -- reorder assumes order is irrelevant
def add_vectr_point {f : fm K} {s : spc K f } (v : vectr K s) (p : point K s) : point K s := 
    mk_point' K s (v.to_vec +ᵥ p.to_pt)

def aff_vectr_group_action : vectr K s → point K s → point K s := add_vectr_point K
instance : has_vadd (vectr K s) (point K s) := ⟨aff_vectr_group_action K⟩

lemma zero_vectr_vadd'_a1 : ∀ p : point K s, (0 : vectr K s) +ᵥ p = p := sorry
lemma vectr_add_assoc'_a1 : ∀ (g1 g2 : vectr K s) (p : point K s), g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p := sorry
instance vectr_add_action: add_action (vectr K s) (point K s) := 
⟨ aff_vectr_group_action K, zero_vectr_vadd'_a1 K, vectr_add_assoc'_a1 K ⟩ 

def aff_point_group_sub : point K s → point K s → vectr K s := sub_point_point K
instance point_has_vsub : has_vsub (vectr K s) (point K s) := ⟨ aff_point_group_sub K ⟩ 

instance : nonempty (point K s) := ⟨mk_point K s 0⟩

lemma point_vsub_vadd_a1 : ∀ (p1 p2 : (point K s)), (p1 -ᵥ p2) +ᵥ p2 = p1 := sorry
lemma point_vadd_vsub_a1 : ∀ (g : vectr K s) (p : point K s), g +ᵥ p -ᵥ p = g := sorry
instance aff_point_torsor : add_torsor (vectr K s) (point K s) := 
⟨ 
    aff_vectr_group_action K,
    zero_vectr_vadd'_a1 K,    -- add_action
    vectr_add_assoc'_a1 K,   -- add_action
    aff_point_group_sub K,    -- has_vsub
    point_vsub_vadd_a1 K,     -- add_torsor
    point_vadd_vsub_a1 K,     -- add_torsor
⟩

open_locale affine
instance : affine_space (vectr K s) (point K s) := aff_point_torsor K
