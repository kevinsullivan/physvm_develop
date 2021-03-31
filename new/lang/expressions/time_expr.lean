import .expr_base
import ...phys.time.time

namespace lang.time

universes u
variables 
  (K : Type u) [field K] [inhabited K] 
  {f : fm K TIME} {sp : spc K f} 

/-
Duration
-/
structure duration_var {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f) extends var 

inductive duration_expr {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f) : Type u
| lit (v : duration sp) : duration_expr
| var (v : duration_var sp) : duration_expr

abbreviation duration_env {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f) := 
  duration_var sp → duration sp

abbreviation duration_eval {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f)  := 
  duration_env sp → duration_var sp → duration sp


/-
Time
-/
structure time_var {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f) extends var

inductive time_expr {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f) : Type u
| lit (p : time sp) : time_expr
| var (v : time_var sp) : time_expr

abbreviation time_env {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f)  := 
  time_var sp → time sp

abbreviation time_eval {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f)  := 
  time_env sp → time_var sp → time sp

/-
ANDREW:

FUNCTION_NAME' (added ') is the suggested implementation version discussed earlier.

-/

def add_dur_expr_dur_expr (v1 v2 : duration_expr sp) : duration_expr sp := 
  sorry

def add_dur_expr_dur_expr' {ev : duration_env sp} (v1 v2 : duration_expr sp) : duration_expr sp := 
  begin
    cases v1,
    { 
      cases v2,
      {
        exact (duration_expr.lit (v1 +ᵥ v2))
      },
      {
        exact (duration_expr.lit ((ev v2) +ᵥ v1))
      }
    },
    { 
      cases v2,
      {
        exact (duration_expr.lit ((ev v1) +ᵥ v2))
      },
      {
        exact (duration_expr.lit ((ev v1) +ᵥ (ev v2)))
      }
    }

  end
def smul_dur_expr' {ev : duration_env sp} (k : K) (v : duration_expr sp) : duration_expr sp := 
  begin
    intros,
    induction v,
    case duration_expr.lit : l {
      exact duration_expr.lit(k•l)
    },
    case duration_expr.var : v {
      exact duration_expr.lit(ev v)
    }

  end
def smul_dur_expr (k : K) (v : duration_expr sp) : duration_expr sp := sorry

def neg_dur_expr (v : duration_expr sp) : duration_expr sp := 
    sorry

def neg_dur_expr' {ev : duration_env sp} (v : duration_expr sp) : duration_expr sp := 
begin
    intros,
    induction v,
    case duration_expr.lit : l {
      exact duration_expr.lit(-l)
    },
    case duration_expr.var : v {
      exact duration_expr.lit(-ev v)
    }

end

def sub_dur_expr_dur_expr (v1 v2 : duration_expr sp) : duration_expr sp :=    -- v1-v2
    sorry

def sub_dur_expr_dur_expr' {ev : duration_env sp} (v1 v2 : duration_expr sp) : duration_expr sp :=    -- v1-v2
begin
    intros,
    cases v1,
    {
      cases v2,
      {
        exact (duration_expr.lit (v1 -ᵥ v2))
      },
      {
        exact (duration_expr.lit (v1 -ᵥ ev v2))
      }
    },
    { 
      cases v2,
      {
        exact (duration_expr.lit ((ev v1) -ᵥ v2))
      },
      {
        exact (duration_expr.lit ((ev v1) -ᵥ (ev v2)))
      }
    }

end
-- See unframed file for template for proving vector_space

instance has_add_dur_expr : has_add (duration_expr sp) := ⟨ add_dur_expr_dur_expr K ⟩
lemma add_assoc_dur_expr : ∀ a b c : duration_expr sp, a + b + c = a + (b + c) := sorry
instance add_semigroup_dur_expr : add_semigroup (duration_expr sp) := ⟨ add_dur_expr_dur_expr K, add_assoc_dur_expr K⟩ 

def dur_expr_zero  := duration_expr.lit (mk_duration sp 0)
instance has_zero_dur_expr : has_zero (duration_expr sp) := ⟨dur_expr_zero K⟩

lemma zero_add_dur_expr : ∀ a : duration_expr sp, 0 + a = a := sorry
lemma add_zero_dur_expr : ∀ a : duration_expr sp, a + 0 = a := sorry
instance add_monoid_dur_expr : add_monoid (duration_expr sp) := ⟨ 
    -- add_semigroup
    add_dur_expr_dur_expr K, 
    add_assoc_dur_expr K, 
    -- has_zero
    dur_expr_zero K,
    -- new structure 
    @zero_add_dur_expr K _ _ f sp, 
    add_zero_dur_expr K
⟩

instance has_neg_dur_expr : has_neg (duration_expr sp) := ⟨neg_dur_expr K⟩
instance has_sub_dur_expr : has_sub (duration_expr sp) := ⟨ sub_dur_expr_dur_expr K⟩ 
lemma sub_eq_add_neg_dur_expr : ∀ a b : duration_expr sp, a - b = a + -b := sorry
instance sub_neg_monoid_dur_expr : sub_neg_monoid (duration_expr sp) := ⟨ 
    add_dur_expr_dur_expr K, add_assoc_dur_expr K, dur_expr_zero K, 
    zero_add_dur_expr K, 
    add_zero_dur_expr K, -- add_monoid
    neg_dur_expr K,                                                                  -- has_neg
    sub_dur_expr_dur_expr K,                                                              -- has_sub
    sub_eq_add_neg_dur_expr K,                                                       -- new
⟩ 

lemma add_left_neg_dur_expr : ∀ a : duration_expr sp, -a + a = 0 := sorry
instance : add_group (duration_expr sp) := ⟨
    -- sub_neg_monoid
    add_dur_expr_dur_expr K, add_assoc_dur_expr K, dur_expr_zero K, zero_add_dur_expr K, add_zero_dur_expr K, -- add_monoid
    neg_dur_expr K,                                                                  -- has_neg
    sub_dur_expr_dur_expr K,                                                              -- has_sub
    sub_eq_add_neg_dur_expr K, 
    -- new
    add_left_neg_dur_expr K,
⟩ 

lemma add_comm_dur_expr : ∀ a b : duration_expr sp, a + b = b + a := sorry
instance add_comm_semigroup_dur_expr : add_comm_semigroup (duration_expr sp) := ⟨
    -- add_semigroup
    add_dur_expr_dur_expr K, 
    add_assoc_dur_expr K,
    add_comm_dur_expr K,
⟩

instance add_comm_monoid_dur_expr : add_comm_monoid (duration_expr sp) := ⟨
-- add_monoid
    -- add_semigroup
    add_dur_expr_dur_expr K, 
    add_assoc_dur_expr K, 
    -- has_zero
    dur_expr_zero K,
    -- new structure 
    zero_add_dur_expr K, 
    add_zero_dur_expr K,
-- add_comm_semigroup (minus repeats)
    add_comm_dur_expr K,
⟩

instance has_scalar_dur_expr : has_scalar K (duration_expr sp) := ⟨
smul_dur_expr K,
⟩

lemma one_smul_dur_expr : ∀ b : duration_expr sp, (1 : K) • b = b := sorry
lemma mul_smul_dur_expr : ∀ (x y : K) (b : duration_expr sp), (x * y) • b = x • y • b := sorry
instance mul_action_dur_expr : mul_action K (duration_expr sp) := ⟨
one_smul_dur_expr K,
mul_smul_dur_expr K,
⟩ 

lemma smul_add_dur_expr : ∀(r : K) (x y : duration_expr sp), r • (x + y) = r • x + r • y := sorry
lemma smul_zero_dur_expr : ∀(r : K), r • (0 : duration_expr sp) = 0 := sorry
instance distrib_mul_action_K_dur_exprKx : distrib_mul_action K (duration_expr sp) := ⟨
smul_add_dur_expr K,
smul_zero_dur_expr K,
⟩ 

-- renaming vs template due to clash with name "s" for prevailing variable
lemma add_smul_dur_expr : ∀ (a b : K) (x : duration_expr sp), (a + b) • x = a • x + b • x := sorry
lemma zero_smul_dur_expr : ∀ (x : duration_expr sp), (0 : K) • x = 0 := sorry
instance semimodule_K_durationK : semimodule K (duration_expr sp) := ⟨ add_smul_dur_expr K, zero_smul_dur_expr  K⟩ 

instance add_comm_group_dur_expr : add_comm_group (duration_expr sp) := ⟨
-- add_group
    add_dur_expr_dur_expr K, add_assoc_dur_expr K, dur_expr_zero K, zero_add_dur_expr K, add_zero_dur_expr K, -- add_monoid
    neg_dur_expr K,                                                                  -- has_neg
    sub_dur_expr_dur_expr K,                                                              -- has_sub
    sub_eq_add_neg_dur_expr K, 
    add_left_neg_dur_expr K,
-- commutativity
    add_comm_dur_expr K,
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


/-
+  : d s -> d s -> d s
•  : K -> d s -> d s
+ᵥ : d s -> t s -> t s 
-ᵥ : t s -> t s -> d s

Here s is an affine coordinate 
space on TIME. Otherwise we've
got time points and durations,
within, but not across, spaces.
-/


/-
Transform
-/
structure transform_var {K : Type u} [field K] [inhabited K] 
  {f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2 : spc K f2) extends var

inductive transform_expr {K : Type u} [field K] [inhabited K] 
  {f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2 : spc K f2) : Type u
| lit (p : time.time_transform sp1 sp2) : transform_expr
| var (v : transform_var sp1 sp2) : transform_expr

abbreviation transform_env {K : Type u} [field K] [inhabited K] 
  {f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2 : spc K f2)  := 
  transform_var sp1 sp2 → time.time_transform sp1 sp2

abbreviation transform_eval  {K : Type u} [field K] [inhabited K] 
  {f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2 : spc K f2) := 
  transform_env sp1 sp2 → transform_var sp1 sp2 → time.time_transform sp1 sp2

/-
Overall environment

--omitting transforms from environment for now, which will make
--env.env, cmd, and etc. , even more complicated in terms of types
--TODO: Go ahead and complete the environment. Thanks! --Kevin
-/
structure env {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f) :=
  (d : duration_env sp )
  (t : time_env sp )

def env.init : env sp :=
  ⟨
    (λv, ⟨mk_vectr sp 1⟩),
    (λv, ⟨mk_point sp 0⟩)
  ⟩

end lang.time
