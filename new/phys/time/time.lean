import ..phys_dimensions
import linear_algebra.affine_space.basic
import ...math.aff1Kcoord.aff1Kcoord_std

open_locale affine

/-
Framed points, vectors, frames
-/

section foo 

universes u --v w
variables 
{K : Type u} [field K] [inhabited K] 

/-
Add frames and (coordinate) spaces based on frames
-/


-- points in time
structure time {f : fm K TIME} (s : spc K f ) extends point s 
def mk_time' {f : fm K TIME} (s : spc K f ) (p : point s) : time s := time.mk p  
def mk_time {f : fm K TIME} (s : spc K f ) (k : K) : time s := time.mk (mk_point s k) 

-- intervals in time
structure duration {f : fm K TIME} (s : spc K f ) extends vectr s 
def mk_duration' {f : fm K TIME} (s : spc K f ) (v : vectr s) : duration s := duration.mk v
def mk_duration  {f : fm K TIME} (s : spc K f ) (k : K) : duration s := duration.mk (mk_vectr s k) 

-- note that we don't extend fm
def mk_time_frame {parent : fm K TIME} {s : spc K parent} (p : time s) (v : duration s) :=
fm.deriv TIME (p.to_point.to_pt, v.to_vectr.to_vec) parent   -- TODO: make sure v ≠ 0

end foo

section bar 

universes u --v w
variables 
(K : Type u) [field K] [inhabited K] 

def time_std_frame : fm K TIME := fm.base TIME
def time_std_space := mk_space K (time_std_frame K)

/-
    *************************************
    Instantiate vector_space K (vector K)
    *************************************
-/

namespace time
variables {f : fm K TIME} {s : spc K f } 

def add_vectr_vectr (v1 v2 : duration s) : duration s := 
    mk_duration' s (v1.to_vectr + v2.to_vectr)
def smul_vectr (k : K) (v : duration s) : duration s := 
    mk_duration' s (k • v.to_vectr)
def neg_vectr (v : duration s) : duration s := 
    mk_duration' s ((-1 : K) • v.to_vectr)
def sub_vectr_vectr (v1 v2 : duration s) : duration s :=    -- v1-v2
    add_vectr_vectr K v1 (neg_vectr K v2)

-- See unframed file for template for proving vector_space

instance has_add_vectr : has_add (duration s) := ⟨ add_vectr_vectr K ⟩
lemma add_assoc_vectr : ∀ a b c : duration s, a + b + c = a + (b + c) := sorry
instance add_semigroup_vectr : add_semigroup (duration s) := ⟨ add_vectr_vectr K, add_assoc_vectr K⟩ 

def vectr_zero  := mk_duration s 0
instance has_zero_vectr : has_zero (duration s) := ⟨vectr_zero K⟩

lemma zero_add_vectr : ∀ a : duration s, 0 + a = a := sorry
lemma add_zero_vectr : ∀ a : duration s, a + 0 = a := sorry
instance add_monoid_vectr : add_monoid (duration s) := ⟨ 
    -- add_semigroup
    add_vectr_vectr K, 
    add_assoc_vectr K, 
    -- has_zero
    vectr_zero K,
    -- new structure 
    @zero_add_vectr K _ _ f s, 
    add_zero_vectr K
⟩

instance has_neg_vectr : has_neg (duration s) := ⟨neg_vectr K⟩
instance has_sub_vectr : has_sub (duration s) := ⟨ sub_vectr_vectr K⟩ 
lemma sub_eq_add_neg_vectr : ∀ a b : duration s, a - b = a + -b := sorry
instance sub_neg_monoid_vectr : sub_neg_monoid (duration s) := ⟨ 
    add_vectr_vectr K, add_assoc_vectr K, vectr_zero K, 
    zero_add_vectr K, 
    add_zero_vectr K, -- add_monoid
    neg_vectr K,                                                                  -- has_neg
    sub_vectr_vectr K,                                                              -- has_sub
    sub_eq_add_neg_vectr K,                                                       -- new
⟩ 

lemma add_left_neg_vectr : ∀ a : duration s, -a + a = 0 := sorry
instance : add_group (duration s) := ⟨
    -- sub_neg_monoid
    add_vectr_vectr K, add_assoc_vectr K, vectr_zero K, zero_add_vectr K, add_zero_vectr K, -- add_monoid
    neg_vectr K,                                                                  -- has_neg
    sub_vectr_vectr K,                                                              -- has_sub
    sub_eq_add_neg_vectr K, 
    -- new
    add_left_neg_vectr K,
⟩ 

lemma add_comm_vectr : ∀ a b : duration s, a + b = b + a := sorry
instance add_comm_semigroup_vectr : add_comm_semigroup (duration s) := ⟨
    -- add_semigroup
    add_vectr_vectr K, 
    add_assoc_vectr K,
    add_comm_vectr K,
⟩

instance add_comm_monoid_vectr : add_comm_monoid (duration s) := ⟨
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

instance has_scalar_vectr : has_scalar K (duration s) := ⟨
smul_vectr K,
⟩

lemma one_smul_vectr : ∀ b : duration s, (1 : K) • b = b := sorry
lemma mul_smul_vectr : ∀ (x y : K) (b : duration s), (x * y) • b = x • y • b := sorry
instance mul_action_vectr : mul_action K (duration s) := ⟨
one_smul_vectr K,
mul_smul_vectr K,
⟩ 

lemma smul_add_vectr : ∀(r : K) (x y : duration s), r • (x + y) = r • x + r • y := sorry
lemma smul_zero_vectr : ∀(r : K), r • (0 : duration s) = 0 := sorry
instance distrib_mul_action_K_vectrKx : distrib_mul_action K (duration s) := ⟨
smul_add_vectr K,
smul_zero_vectr K,
⟩ 

-- renaming vs template due to clash with name "s" for prevailing variable
lemma add_smul_vectr : ∀ (a b : K) (x : duration s), (a + b) • x = a • x + b • x := sorry
lemma zero_smul_vectr : ∀ (x : duration s), (0 : K) • x = 0 := sorry
instance semimodule_K_durationK : semimodule K (duration s) := ⟨ add_smul_vectr K, zero_smul_vectr  K⟩ 

instance add_comm_group_vectr : add_comm_group (duration s) := ⟨
-- add_group
    add_vectr_vectr K, add_assoc_vectr K, vectr_zero K, zero_add_vectr K, add_zero_vectr K, -- add_monoid
    neg_vectr K,                                                                  -- has_neg
    sub_vectr_vectr K,                                                              -- has_sub
    sub_eq_add_neg_vectr K, 
    add_left_neg_vectr K,
-- commutativity
    add_comm_vectr K,
⟩

instance : vector_space K (duration s) := @time.semimodule_K_durationK K _ _ f s


/-
    ********************
    *** Affine space ***
    ********************
-/


/-
Affine operations
-/
instance : has_add (duration s) := ⟨add_vectr_vectr K⟩
instance : has_zero (duration s) := ⟨vectr_zero K⟩
instance : has_neg (duration s) := ⟨neg_vectr K⟩

/-
Lemmas needed to implement affine space API
-/

def sub_point_point {f : fm K TIME} {s : spc K f } (p1 p2 : time s) : duration s := 
    mk_duration' s (p2.to_point -ᵥ p1.to_point)
def add_point_vectr {f : fm K TIME} {s : spc K f } (p : time s) (v : duration s) : time s := 
    mk_time' s (v.to_vectr +ᵥ p.to_point) -- reorder assumes order is irrelevant
def add_vectr_point {f : fm K TIME} {s : spc K f } (v : duration s) (p : time s) : time s := 
    mk_time' s (v.to_vectr +ᵥ p.to_point)

def aff_vectr_group_action : duration s → time s → time s := add_vectr_point K
instance : has_vadd (duration s) (time s) := ⟨aff_vectr_group_action K⟩

lemma zero_vectr_vadd'_a1 : ∀ p : time s, (0 : duration s) +ᵥ p = p := sorry
lemma vectr_add_assoc'_a1 : ∀ (g1 g2 : duration s) (p : time s), g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p := sorry
instance vectr_add_action: add_action (duration s) (time s) := 
⟨ aff_vectr_group_action K, zero_vectr_vadd'_a1 K, vectr_add_assoc'_a1  K⟩ 

def aff_point_group_sub : time s → time s → duration s := sub_point_point K
instance point_has_vsub : has_vsub (duration s) (time s) := ⟨ aff_point_group_sub K ⟩ 

instance : nonempty (time s) := ⟨mk_time s 0⟩

lemma point_vsub_vadd_a1 : ∀ (p1 p2 : (time s)), (p1 -ᵥ p2) +ᵥ p2 = p1 := sorry
lemma point_vadd_vsub_a1 : ∀ (g : duration s) (p : time s), g +ᵥ p -ᵥ p = g := sorry
instance aff_point_torsor : add_torsor (duration s) (time s) := 
⟨ 
    aff_vectr_group_action K,
    zero_vectr_vadd'_a1 K,    -- add_action
    vectr_add_assoc'_a1 K,   -- add_action
    aff_point_group_sub K,    -- has_vsub
    point_vsub_vadd_a1 K,     -- add_torsor
    point_vadd_vsub_a1 K,     -- add_torsor
⟩

open_locale affine

instance : affine_space (duration s) (time s) := @time.aff_point_torsor K _ _ f s

end time -- ha ha
end bar

--prefer implicit here
universes u
variables 
{K : Type u} [field K] [inhabited K] 


--extends does not work with abbreviation or def, so the type is ugly.
structure time_transform {K : Type u} [field K] [inhabited K] {f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2 : spc K f2)
  extends ((time sp1) ≃ᵃ[K] (time sp2))
variables {f1 : fm K TIME} {f2 : fm K TIME}  (s2 : spc K f2)
def spc.time_tr (s1 : spc K f1) {f2 : fm K TIME} : Π(s2 : spc K f2), time_transform s1 s2 := --(time s2) ≃ᵃ[K] (time s1) := 
    λ s2,
    let pointtr : (point s1) ≃ᵃ[K] (point s2)  := s1.tr s2 in
        ⟨⟨
            ⟨
                (λ p : time s1, (⟨(pointtr p.to_point : point _)⟩ : time s2)),
                (λ p : time s2, (⟨(pointtr.symm p.to_point : point _)⟩ : time s1)),
                sorry,
                sorry
            ⟩,
            ⟨
                (λv : duration _, (⟨(pointtr.linear v.1 : vectr _)⟩ : duration _)),
                sorry,
               -- (λ v, ⟨v.to_vec⟩),
                sorry,
                (λv : duration _, (⟨(pointtr.symm.linear v.1 : vectr _)⟩ : duration _)),
                sorry,
                sorry
            ⟩,
            sorry
        ⟩⟩

#check s2.time_tr s2
