import .aff1K
import linear_algebra.affine_space.affine_equiv

/-
Framed points, vectors, frames
-/

universes u 

section explicitK

variables 
(K : Type u) [field K] [inhabited K] 

/-
Is this where we root distinctions between affine spaces for different dimensionss?
-/
inductive fm : nat → Type u
| base : Π n, fm n
| deriv : Π n, (prod (pt K) (vec K)) → fm n → fm n  -- TODO: curry all of these args

/-
inductive fm : nat → Type u
| base : ∀ (n : nat), fm n
| deriv : ∀ (n : nat), (prod (pt K) (vec K)) → fm n → fm n
-/

def mk_fm  {n : nat } (p : pt K) (v : vec K) (f : fm K n): fm K n := fm.deriv n (p, v) f 

structure spc {n : nat} (f : fm K n) : Type u       -- interesting specimen, here, btw

def mk_space {n : nat} (f : fm K n) :=
  @spc.mk K _ _ n f 

end explicitK

section implicitK

variables 
{K : Type u} [field K] [inhabited K] 
{n : nat} {f : fm K n} (s : spc K f)

/-
Augment pt and vec types with spaces and frames and
then make operations apply only for objects in same
space (and thus frame).
-/

structure point {f : fm K n} (s : @spc K _ _ n f ) extends pt K
def mk_point' (p : pt K) : point s := point.mk p  
def mk_point (k : K) : point s := point.mk (mk_pt K k)  

def p := mk_point s (3:K)

structure vectr {f : fm K n} (s : spc K f ) extends vec K
def mk_vectr' (v : vec K) : vectr s := vectr.mk v
def mk_vectr (k : K) : vectr s := vectr.mk (mk_vec K k)  

-- note that we don't extend fm
def mk_frame {parent : fm K n} {s : spc K parent}  (p : point s) (v : vectr s) :=
fm.deriv n (p.to_pt, v.to_vec) parent   -- TODO: make sure v ≠ 0 (erasing tyoe info)
                                      -- TODO: snd arg is really a basis for the vs


/-
    *************************************
    Instantiate vector_space K (vector K)
    *************************************
-/

variables v1 v2 : @vectr K _ _ n f s
#check v1.to_vec
#check v2.to_vec + v1.to_vec

def add_vectr_vectr (v1 v2 : vectr s) : vectr s :=  mk_vectr' s (v1.to_vec + v2.to_vec)
def smul_vectr (k : K) (v : vectr s) : vectr s := mk_vectr' s (k • v.to_vec)
def neg_vectr (v : vectr s) : vectr s := mk_vectr' s ((-1 : K) • v.to_vec)
def sub_vectr_vectr (v1 v2 : vectr s) : vectr s := add_vectr_vectr s v1 (neg_vectr s v2)

-- See unframed file for template for proving vector_space

instance has_add_vectr : has_add (vectr s) := ⟨add_vectr_vectr s⟩
lemma add_assoc_vectr : ∀ a b c : vectr s, a + b + c = a + (b + c) := sorry
instance add_semigroup_vectr : add_semigroup (vectr s) := ⟨ add_vectr_vectr s, add_assoc_vectr s⟩ 

def vectr_zero := @mk_vectr K _ _ n f s (0:K)
instance has_zero_vectr : has_zero (vectr s) := ⟨vectr_zero s⟩

lemma zero_add_vectr : ∀ a : vectr s, 0 + a = a := sorry
lemma add_zero_vectr : ∀ a : vectr s, a + 0 = a := sorry
instance add_monoid_vectr : add_monoid (vectr s) := ⟨ 
    -- add_semigroup
    add_vectr_vectr s, 
    add_assoc_vectr s, 
    -- has_zero
    vectr_zero s,
    -- new structure 
    zero_add_vectr s, 
    add_zero_vectr s
⟩

instance has_neg_vectr : has_neg (vectr s) := ⟨ neg_vectr s ⟩
instance has_sub_vectr : has_sub (vectr s) := ⟨ sub_vectr_vectr s ⟩ 
lemma sub_eq_add_neg_vectr : ∀ a b : vectr s, a - b = a + -b := sorry
instance sub_neg_monoid_vectr : sub_neg_monoid (vectr s) := ⟨ 
    add_vectr_vectr s, add_assoc_vectr s, vectr_zero s, zero_add_vectr s, add_zero_vectr s, -- add_monoid
    neg_vectr s,                                                                  -- has_neg
    sub_vectr_vectr s,                                                              -- has_sub
    sub_eq_add_neg_vectr s,                                                       -- new
⟩ 

lemma add_left_neg_vectr : ∀ a : vectr s, -a + a = 0 := sorry
instance : add_group (vectr s) := ⟨
    -- sub_neg_monoid
    add_vectr_vectr s, add_assoc_vectr s, vectr_zero s, zero_add_vectr s, add_zero_vectr s, -- add_monoid
    neg_vectr s,                                                                  -- has_neg
    sub_vectr_vectr s,                                                              -- has_sub
    sub_eq_add_neg_vectr s, 
    -- new
    add_left_neg_vectr s,
⟩ 

lemma add_comm_vectr : ∀ a b : vectr s, a + b = b + a := sorry
instance add_comm_semigroup_vectr : add_comm_semigroup (vectr s) := ⟨
    -- add_semigroup
    add_vectr_vectr s, 
    add_assoc_vectr s,
    add_comm_vectr s,
⟩

instance add_comm_monoid_vectr : add_comm_monoid (vectr s) := ⟨
-- add_monoid
    -- add_semigroup
    add_vectr_vectr s, 
    add_assoc_vectr s, 
    -- has_zero
    vectr_zero s,
    -- new structure 
    zero_add_vectr s, 
    add_zero_vectr s,
-- add_comm_semigroup (minus repeats)
    add_comm_vectr s,
⟩

instance has_scalar_vectr : has_scalar K (vectr s) := ⟨
smul_vectr s,
⟩

lemma one_smul_vectr : ∀ b : vectr s, (1 : K) • b = b := sorry
lemma mul_smul_vectr : ∀ (x y : K) (b : vectr s), (x * y) • b = x • y • b := sorry
instance mul_action_vectr : mul_action K (vectr s) := ⟨
one_smul_vectr s,
mul_smul_vectr s,
⟩ 

lemma smul_add_vectr : ∀(r : K) (x y : vectr s), r • (x + y) = r • x + r • y := sorry
lemma smul_zero_vectr : ∀(r : K), r • (0 : vectr s) = 0 := sorry
instance distrib_mul_action_K_vectrK : distrib_mul_action K (vectr s) := ⟨
smul_add_vectr s,
smul_zero_vectr s,
⟩ 

-- renaming vs template due to clash with name "s" for prevailing variable
lemma add_smul_vectr : ∀ (a b : K) (x : vectr s), (a + b) • x = a • x + b • x := sorry
lemma zero_smul_vectr : ∀ (x : vectr s), (0 : K) • x = 0 := sorry
instance semimodule_K_vectrK : semimodule K (vectr s) := ⟨ 
    add_smul_vectr s, 
    zero_smul_vectr s, 
⟩ 

instance add_comm_group_vectr : add_comm_group (vectr s) := ⟨
-- add_group
    add_vectr_vectr s, add_assoc_vectr s, vectr_zero s, zero_add_vectr s, add_zero_vectr s, -- add_monoid
    neg_vectr s,                                                                  -- has_neg
    sub_vectr_vectr s,                                                              -- has_sub
    sub_eq_add_neg_vectr s, 
    add_left_neg_vectr s,
-- commutativity
    add_comm_vectr s,
⟩

instance : vector_space K (vectr s) := semimodule_K_vectrK s

/-
    ********************
    *** Affine space ***
    ********************
-/

/-
Affine operations
-/
instance : has_add (vectr s) := ⟨add_vectr_vectr s⟩
instance : has_zero (vectr s) := ⟨vectr_zero s⟩
instance : has_neg (vectr s) := ⟨neg_vectr s⟩

/-
Lemmas needed to implement affine space API
-/

def sub_point_point (p1 p2 : point s) : vectr s := mk_vectr' s (p2.to_pt -ᵥ p1.to_pt)
def add_point_vectr {f : fm K n} {s : spc K f } (p : point s) (v : vectr s) : point s := 
    mk_point' s (v.to_vec +ᵥ p.to_pt) -- reorder assumes order is irrelevant
def add_vectr_point {f : fm K n} {s : spc K f } (v : vectr s) (p : point s) : point s := 
    mk_point' s (v.to_vec +ᵥ p.to_pt)

def aff_vectr_group_action : vectr s → point s → point s := add_vectr_point
instance : has_vadd (vectr s) (point s) := ⟨aff_vectr_group_action s⟩

lemma zero_vectr_vadd'_a1 : ∀ p : point s, (0 : vectr s) +ᵥ p = p := sorry
lemma vectr_add_assoc'_a1 : ∀ (g1 g2 : vectr s) (p : point s), g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p := sorry
instance vectr_add_action: add_action (vectr s) (point s) := 
⟨ aff_vectr_group_action s, zero_vectr_vadd'_a1 s, vectr_add_assoc'_a1 s ⟩ 

def aff_point_group_sub : point s → point s → vectr s := sub_point_point s
instance point_has_vsub : has_vsub (vectr s) (point s) := ⟨ aff_point_group_sub s ⟩ 

instance : nonempty (point s) := ⟨mk_point s 0⟩

lemma point_vsub_vadd_a1 : ∀ (p1 p2 : (point s)), (p1 -ᵥ p2) +ᵥ p2 = p1 := sorry
lemma point_vadd_vsub_a1 : ∀ (g : vectr s) (p : point s), g +ᵥ p -ᵥ p = g := sorry
instance aff_point_torsor : add_torsor (vectr s) (point s) := 
⟨ 
    aff_vectr_group_action s,
    zero_vectr_vadd'_a1 s,    -- from add_action
    vectr_add_assoc'_a1 s,    -- from add_action
    aff_point_group_sub s,    -- from has_vsub
    point_vsub_vadd_a1 s,     -- from add_torsor
    point_vadd_vsub_a1 s,     -- from add_torsor
⟩

open_locale affine
instance : affine_space (vectr s) (point s) := aff_point_torsor s

variables {f1 : fm K} {f2 : fm K} (s1 : spc K f1) (s2 : spc K f2)

abbreviation raw_tr := (pt K) ≃ᵃ[K] (pt K)
abbreviation fm_tr := (point s1) ≃ᵃ[K] (point s2)

def to_base_helper' : fm K → @raw_tr K _ _
| (fm.base) := ⟨
            ⟨
                (λ p, p),
                (λ p, p),
                sorry,
                sorry
            ⟩,
            ⟨
                (λ v, v),
                sorry,
               -- (λ v, ⟨v.to_vec⟩),
                sorry,
                (λ v, v),
                sorry,
                sorry
            ⟩,
            sorry
        ⟩
| (fm.deriv c parent) := (⟨
            ⟨/-.1 and .2 only refer to K coordinates-/
                λp, ⟨(p.to_prod.1*c.snd.to_prod.1 +  p.to_prod.2*c.fst.to_prod.1, p.to_prod.1*c.snd.to_prod.2 + p.to_prod.2*c.snd.to_prod.2),sorry⟩,
                sorry,
                sorry,
                sorry
            ⟩,
            ⟨
                λv, ⟨(v.to_prod.1*c.snd.to_prod.1, 0),sorry⟩,
                sorry,
                sorry,
                sorry,
                sorry,
                sorry
            ⟩,
            sorry
        ⟩ : @raw_tr K _ _).trans (to_base_helper' parent)

--def to_base_helper : spc K f1 → @raw_tr K _ _
 

def spc.to_base (s1 : spc K f1) : @raw_tr K _ _ := to_base_helper' f1


def spc.tr (s1 : spc K f1) : fm_tr s1 s2 := 
    let rawtr : @raw_tr K _ _ := s1.to_base.trans s2.to_base.symm in
                ⟨
            ⟨
                (λ p : point s1, (⟨(rawtr p.1 : pt K)⟩ : point s2)),
                (λ p : point s2, (⟨(rawtr p.1 : pt K)⟩ : point s1)),
                sorry,
                sorry
            ⟩,
            ⟨
                (λv : vectr s1, (⟨(rawtr.linear v.1 : vec K)⟩ : vectr s2)),
                sorry,
               -- (λ v, ⟨v.to_vec⟩),
                sorry,
                (λv : vectr s2, (⟨(rawtr.linear v.1 : vec K)⟩ : vectr s1)),
                sorry,
                sorry
            ⟩,
            sorry
        ⟩

end implicitK

-- TODO: clean up naming in this file