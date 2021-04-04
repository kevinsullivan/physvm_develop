import .expr_base
import ...phys.time.time

namespace lang.time

universes u
variables 
  (K : Type u) [field K] [inhabited K] 
  {f : fm K TIME} {sp : spc K f} 

/-
Concern? This space parameter still needs to be here for now. Any environment function needs to know.
Response: It's ok. Consistent with the system design and operation.
-/
structure duration_var {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f) extends var 

/-
Time
-/
structure time_var {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f) extends var

/-
Begin: Earlier attempts at induction and time expressions, revealing some interesting situations.
-/

/-
mutual inductive duration_expr, time_expr {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f) 
with duration_expr : Type u
| lit (v : duration sp) : duration_expr
| var (v : duration_var sp) : duration_expr
| add_dur_dur (d1 : duration_expr) (d2 : duration_expr) : duration_expr
| neg_dur (d : duration_expr) : duration_expr
| sub_dur_dur (d1 : duration_expr) (d2 : duration_expr) : duration_expr
| sub_time_time (t1 : time_expr) (t2 : time_expr) : duration_expr
| smul_dur (k : K) (d : duration_expr) : duration_expr
with time_expr : Type u
| lit (p : time sp) : time_expr
| var (v : time_var sp) : time_expr
| add_dur_time (d : duration_expr) (t : time_expr) : time_expr
-/

/-
mutual inductive duration_expr, time_expr
with duration_expr : Π(K : Type u) [field K] [inhabited K], Type (u+1)
| zero : duration_expr
| one : duration_expr
| lit {f : fm K TIME} {sp : spc K f} (v : duration sp) : duration_expr
| var {f : fm K TIME} {sp : spc K f} (v : duration_var sp) : duration_expr
| add_dur_dur (d1 : duration_expr) (d2 : duration_expr) : duration_expr 
| neg_dur (d : duration_expr) : duration_expr
| sub_dur_dur (d1 : duration_expr) (d2 : duration_expr) : duration_expr
| sub_time_time (t1 : time_expr K) (t2 : time_expr K) : duration_expr
| smul_dur (k : K) (d : duration_expr) : duration_expr
with time_expr : Π(K : Type u) [field K] [inhabited K], Type (u+1)
| lit {f : fm K TIME} {sp : spc K f} (p : time sp) : time_expr K
| var {f : fm K TIME} {sp : spc K f} (v : time_var sp) : time_expr K
| add_dur_time (d : duration_expr) (t : time_expr K) : time_expr K
-/

set_option trace.app_builder true
--set_option pp.raw true
--set_option pp.raw.maxDepth 10
--set_option pp.universes true
--set_option pp.all true
--#help options
--set_option trace.inductive_compiler.mutual.sizeof true
--set_option trace.type_context.unification_hint true
--set_option trace.inductive.unify true
--help options

/-
[app_builder] failed to create an 'sizeof'-application, 
failed to solve unification constraint for #1 argument (?x_0 =?= fm K TIME)
-/
/-
mutual inductive duration_expr, time_expr --(K : Type u) [field K] [inhabited K]
with duration_expr : Type (u+1)
| zero : duration_expr
| one : duration_expr
| lit {K : Type u} [field K] [inhabited K] {f1 : fm K TIME} {sp : spc K f1} (v : duration sp) : duration_expr
with time_expr  : Type (u+1)
| lit {K : Type u} [field K] [inhabited K] {f : fm K TIME} {sp : spc K f} (p : time sp) : time_expr
-/

/-
[app_builder] failed to create an 'sizeof'-application, 
failed to solve unification constraint for #1 argument (?x_0 =?= fm K TIME)
-/
/-
mutual inductive duration_expr, time_expr --(K : Type u) [field K] [inhabited K]
with duration_expr : Type (u+1)
| zero : /-Π (K : Type u) [field K] [inhabited K],-/ duration_expr
| one : /-Π (K : Type u) [field K] [inhabited K],-/ duration_expr
| lit : Π /-{K : Type u} [field K] [inhabited K]-/ {f : fm K TIME} {sp : spc K f} (d : duration sp), duration_expr
| var : Π /-{K : Type u} [field K] [inhabited K]-/ {f : fm K TIME} {sp : spc K f}, Π (v : duration_var sp), duration_expr
| add_dur_dur : Π (d1 d2 : duration_expr), duration_expr 
| neg_dur : Π (d : duration_expr), duration_expr
| sub_dur_dur : Π (d1 d2 : duration_expr), duration_expr
| sub_time_time : Π (t1 t2 : time_expr), duration_expr
| smul_dur : /-Π {K : Type u} [field K] [inhabited K],-/ Π (k : K), Π (d : duration_expr), duration_expr
with time_expr  : Type (u+1)
| lit : Π/-{K : Type u} [field K] [inhabited K]-/ {f : fm K TIME} {sp : spc K f} (t : time sp), time_expr
| var : Π/-{K : Type u} [field K] [inhabited K]-/ {f : fm K TIME} {sp : spc K f} (v : time_var sp),  time_expr
| add_dur_time : Π (d : duration_expr) (t : time_expr), time_expr
-/

/-
Current attempt. Still with some blockers below. 
-/
mutual inductive duration_expr, time_expr --(K : Type u) [field K] [inhabited K]
with duration_expr : Type (u+1)
| zero : Π (K : Type u) [field K] [inhabited K], duration_expr
| one : Π (K : Type u) [field K] [inhabited K], duration_expr
| lit : Π {K : Type u} [field K] [inhabited K] {f : fm K TIME} {sp : spc K f} (d : duration sp), duration_expr
| var : Π {K : Type u} [field K] [inhabited K] {f : fm K TIME} {sp : spc K f}, Π (v : duration_var sp), duration_expr
| add_dur_dur : Π (d1 d2 : duration_expr), duration_expr 
| neg_dur : Π (d : duration_expr), duration_expr
| sub_dur_dur : Π (d1 d2 : duration_expr), duration_expr
| sub_time_time : Π (t1 t2 : time_expr), duration_expr
| smul_dur : Π {K : Type u} [field K] [inhabited K], Π (k : K), Π (d : duration_expr), duration_expr
with time_expr  : Type (u+1)
| lit : Π{K : Type u} [field K] [inhabited K] {f : fm K TIME} {sp : spc K f} (t : time sp), time_expr
| var : Π{K : Type u} [field K] [inhabited K] {f : fm K TIME} {sp : spc K f} (v : time_var sp),  time_expr
| add_dur_time : Π (d : duration_expr) (t : time_expr), time_expr
--def d11 := duration_expr1.lit K f

def mt : ∀k : duration_expr, Type :=
begin
  intros,
  cases k,
  repeat {
  exact nat
  }
end

/-
Another attempt?
-/
/-
mutual inductive duration_expr, time_expr
with duration_expr : Π(K : Type u) [field K] [inhabited K], Type (u+1)
| zero : duration_expr
| one : duration_expr
| lit {f : fm K TIME} {sp : spc K f} (v : duration sp) : duration_expr
| var {f : fm K TIME} {sp : spc K f} (v : duration_var sp) : duration_expr
| add_dur_dur (d1 : duration_expr) (d2 : duration_expr) : duration_expr 
| neg_dur (d : duration_expr) : duration_expr
| sub_dur_dur (d1 : duration_expr) (d2 : duration_expr) : duration_expr
| sub_time_time (t1 : time_expr K) (t2 : time_expr K) : duration_expr
| smul_dur (k : K) (d : duration_expr) : duration_expr
with time_expr : Π(K : Type u) [field K] [inhabited K], Type (u+1)
| lit {f : fm K TIME} {sp : spc K f} (p : time sp) : time_expr K
| var {f : fm K TIME} {sp : spc K f} (v : time_var sp) : time_expr K
| add_dur_time (d : duration_expr) (t : time_expr K) : time_expr K
-/

abbreviation duration_env {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f) := 
  duration_var sp → duration sp

abbreviation duration_eval {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f)  := 
  duration_env sp → duration_expr → duration sp

abbreviation time_env {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f)  := 
  time_var sp → time sp

abbreviation time_eval {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f)  := 
  time_env sp → time_expr → time sp

/-
ANDREW:
FUNCTION_NAME' (added ') is the suggested implementation version discussed earlier.
-/

/-
Duration expressions: add dur dur, smul scal dur
-/

def add_dur_expr_dur_expr (v1 v2 : duration_expr) : duration_expr := 
  duration_expr.add_dur_dur v1 v2

variables {T : Type u} [field T] [inhabited T] (k : T) (dd : duration_expr)

#check (λx:ℕ, dd)
def stdlit := duration_expr.lit (mk_duration (time_std_space K) 1)
#check duration_expr.smul_dur (1:K) (stdlit K)
#check duration_expr

def smul_dur_expr {K : Type u} [field K] [inhabited K] (k : K) (v : duration_expr) : duration_expr := 
    duration_expr.smul_dur k v

variables (my_expr : duration_expr) (kk : K)

/-
type mismatch at application
  smul_dur_expr kk my_expr
term
  my_expr
has type
  lang.time.duration_expr.{u_2} : Type (u_2+1)
but is expected to have type
  lang.time.duration_expr.{u} : Type (u+1)
All Messages (76)
-/

#check my_expr        -- duration_expr
#check @duration_expr  -- Type (u_3+1)
#check @smul_dur_expr 
/- 
Π {K : Type u} [_inst_5 : field K] [_inst_6 : inhabited K], 
   K → duration_expr → duration_expr
-/
#check smul_dur_expr _ my_expr

def neg_dur_expr (v : duration_expr) : duration_expr := 
    duration_expr.neg_dur v
/-
def neg_dur_expr' {ev : duration_env sp} (v : duration_expr) : duration_expr := 
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
-/
def sub_dur_expr_dur_expr (v1 v2 : duration_expr) : duration_expr :=    -- v1-v2
    duration_expr.sub_dur_dur v1 v2
/-
def sub_dur_expr_dur_expr' {ev : duration_env sp} (v1 v2 : duration_expr) : duration_expr :=    -- v1-v2
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

end-/
-- See unframed file for template for proving vector_space

instance has_add_dur_expr : has_add (duration_expr) := ⟨ add_dur_expr_dur_expr ⟩
lemma add_assoc_dur_expr : ∀ a b c : duration_expr, a + b + c = a + (b + c) := sorry
instance add_semigroup_dur_expr : add_semigroup (duration_expr) := ⟨ add_dur_expr_dur_expr, add_assoc_dur_expr⟩ 

def dur_expr_zero  := duration_expr.zero
instance has_zero_dur_expr : has_zero (duration_expr) := ⟨dur_expr_zero K⟩

--optin class.instance_max_depth
--set_option trace.class_instances true


lemma zero_add_dur_expr : ∀ a : duration_expr, (0 : duration_expr) + a = a := sorry
lemma add_zero_dur_expr : ∀ a : duration_expr, a + 0 = a := sorry
instance add_monoid_dur_expr {f : fm K TIME} {sp : spc K f} : add_monoid (duration_expr) := ⟨ 
    -- add_semigroup
    add_dur_expr_dur_expr, 
    add_assoc_dur_expr, 
    -- has_zero
    dur_expr_zero,
    -- new structure 
    zero_add_dur_expr, 
    add_zero_dur_expr
⟩

instance has_neg_dur_expr : has_neg (duration_expr) := ⟨neg_dur_expr⟩
instance has_sub_dur_expr : has_sub (duration_expr) := ⟨ sub_dur_expr_dur_expr⟩ 
lemma sub_eq_add_neg_dur_expr : ∀ a b : duration_expr, a - b = a + -b := sorry
instance sub_neg_monoid_dur_expr : sub_neg_monoid (duration_expr) := ⟨ 
    add_dur_expr_dur_expr, add_assoc_dur_expr, dur_expr_zero, 
    zero_add_dur_expr, 
    add_zero_dur_expr, -- add_monoid
    neg_dur_expr,                                                                  -- has_neg
    sub_dur_expr_dur_expr,                                                              -- has_sub
    sub_eq_add_neg_dur_expr,                                                       -- new
⟩ 

lemma add_left_neg_dur_expr : ∀ a : duration_expr, -a + a = 0 := sorry
instance : add_group (duration_expr) := ⟨
    -- sub_neg_monoid
    add_dur_expr_dur_expr, add_assoc_dur_expr, dur_expr_zero, zero_add_dur_expr, add_zero_dur_expr, -- add_monoid
    neg_dur_expr,                                                                  -- has_neg
    sub_dur_expr_dur_expr,                                                              -- has_sub
    sub_eq_add_neg_dur_expr, 
    -- new
    add_left_neg_dur_expr,
⟩ 

lemma add_comm_dur_expr : ∀ a b : duration_expr, a + b = b + a := sorry
instance add_comm_semigroup_dur_expr : add_comm_semigroup (duration_expr) := ⟨
    -- add_semigroup
    add_dur_expr_dur_expr, 
    add_assoc_dur_expr,
    add_comm_dur_expr,
⟩

instance add_comm_monoid_dur_expr : add_comm_monoid (duration_expr) := ⟨
-- add_monoid
    -- add_semigroup
    add_dur_expr_dur_expr, 
    add_assoc_dur_expr, 
    -- has_zero
    dur_expr_zero,
    -- new structure 
    zero_add_dur_expr, 
    add_zero_dur_expr,
-- add_comm_semigroup (minus repeats)
    add_comm_dur_expr,
⟩

instance has_scalar_dur_expr /- {K : Type u} [field K] [inhabited K]-/: has_scalar K duration_expr := ⟨
smul_dur_expr K,
⟩

variables (v : K) (d : duration_expr)

#check v • d

lemma one_smul_dur_expr
  {K : Type u} [field K] [inhabited K] [has_scalar K duration_expr] : ∀ b : duration_expr, 
    --(smul_dur_expr K) 1 b = b := sorry
    (1 : K) • b = b := sorry
lemma mul_smul_dur_expr : ∀ (x y : K) (b : duration_expr), (x * y) • b = x • y • b := sorry
instance mul_action_dur_expr  : mul_action K (duration_expr) := ⟨
one_smul_dur_expr,
mul_smul_dur_expr,
⟩ 

lemma smul_add_dur_expr : ∀(r : K) (x y : duration_expr), r • (x + y) = r • x + r • y := sorry
lemma smul_zero_dur_expr : ∀(r : K), r • (0 : duration_expr) = 0 := sorry
instance distrib_mul_action_K_dur_exprKx : distrib_mul_action K (duration_expr) := ⟨
smul_add_dur_expr,
smul_zero_dur_expr,
⟩ 

-- renaming vs template due to clash with name "s" for prevailing variable
lemma add_smul_dur_expr : ∀ (a b : K) (x : duration_expr), (a + b) • x = a • x + b • x := sorry
lemma zero_smul_dur_expr : ∀ (x : duration_expr), (0 : K) • x = 0 := sorry
instance semimodule_K_durationK : semimodule K (duration_expr) := ⟨ add_smul_dur_expr, zero_smul_dur_expr  K⟩ 

instance add_comm_group_dur_expr : add_comm_group (duration_expr) := ⟨
-- add_group
    add_dur_expr_dur_expr, add_assoc_dur_expr, dur_expr_zero, zero_add_dur_expr, add_zero_dur_expr, -- add_monoid
    neg_dur_expr,                                                                  -- has_neg
    sub_dur_expr_dur_expr,                                                              -- has_sub
    sub_eq_add_neg_dur_expr, 
    add_left_neg_dur_expr,
-- commutativity
    add_comm_dur_expr,
⟩


instance : vector_space K (duration_expr) := sorry


/-
    ********************
    *** Affine space ***
    ********************
-/


/-
Affine operations
-/
instance : has_add (duration_expr) := ⟨add_dur_expr_dur_expr⟩
instance : has_zero (duration_expr) := ⟨dur_expr_zero K⟩
instance : has_neg (duration_expr) := ⟨neg_dur_expr⟩

/-
Lemmas needed to implement affine space API
-/
/-
kernel failed to type check declaration 'sub_time_expr_time_expr' this is usually due to a 
buggy tactic or a bug in the builtin elaborator

ANDREW - THIS LOOKS VERY BAD!
-/

def sub_time_expr_time_expr {f : fm K TIME} {sp : spc K f } (p1 p2 : time_expr) : duration_expr := 
    duration_expr.sub_time_time p1 p2
def add_time_expr_dur_expr {f : fm K TIME} {sp : spc K f } (p : time_expr) (v : duration_expr) : time_expr := 
    time_expr.add_dur_time v p
def add_dur_expr_time_expr {f : fm K TIME} {sp : spc K f } (v : duration_expr) (p : time_expr) : time_expr := 
    time_expr.add_dur_time v p

def aff_dur_expr_group_action : duration_expr → time_expr → time_expr := add_dur_expr_time_expr
instance : has_vadd (duration_expr) (time_expr) := ⟨aff_dur_expr_group_action K⟩

lemma zero_dur_expr_vadd'_a1 : ∀ p : time_expr, (0 : duration_expr) +ᵥ p = p := sorry
lemma dur_expr_add_assoc'_a1 : ∀ (g1 g2 : duration_expr) (p : time_expr), g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p := sorry
instance dur_expr_add_action: add_action (duration_expr) (time_expr) := 
⟨ aff_dur_expr_group_action K, zero_dur_expr_vadd'_a1 K, dur_expr_add_assoc'_a1  K⟩ 

def aff_time_expr_group_sub : time_expr → time_expr → duration_expr := sub_time_expr_time_expr
instance time_expr_has_vsub : has_vsub (duration_expr) (time_expr) := ⟨ aff_time_expr_group_sub K ⟩ 


instance : nonempty (time_expr) := ⟨time_expr.lit (mk_time sp  1)⟩

lemma time_expr_vsub_vadd_a1 : ∀ (p1 p2 : (time_expr)), (p1 -ᵥ p2) +ᵥ p2 = p1 := sorry
lemma time_expr_vadd_vsub_a1 : ∀ (g : duration_expr) (p : time_expr), g +ᵥ p -ᵥ p = g := sorry
instance aff_time_expr_torsor : add_torsor (duration_expr) (time_expr) := 
⟨ 
    aff_dur_expr_group_action K,
    zero_dur_expr_vadd'_a1 K,    -- add_action
    dur_expr_add_assoc'_a1 K,   -- add_action
    aff_time_expr_group_sub K,    -- has_vsub
    time_expr_vsub_vadd_a1 K,     -- add_torsor
    time_expr_vadd_vsub_a1 K,     -- add_torsor
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
/-
inductive transform_expr {K : Type u} [field K] [inhabited K] 
  --{f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2:=sp1 : spc K f2) 
 -- (sp1 : Σf1 : fm K TIME, spc K f1)  (sp2 : Σf2 : fm K TIME, spc K f2 := sp1)
  : Π {f1 : fm K TIME} (sp1 : spc K f1), Π {f2 : fm K TIME} (sp2 : spc K f2), Type u
| lit {f1 : fm K TIME} (sp1 : spc K f1) {f2 : fm K TIME} (sp2 : spc K f2) (p : time_transform sp1 sp2) : transform_expr sp1 sp2
| var (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2) (v : transform_var sp1.2 sp2.2) : transform_expr sp1 sp2
| apply_duration (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2) (v : transform_expr sp1 sp2) (d : duration_expr1.2) : transform_expr sp1 sp2
| compose (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2)  (v : time_transform sp1.2 sp2.2) 
  (sp3 : Σf3 : fm K TIME, spc K f3)  (v : time_transform sp1 sp2) : transform_expr sp1 sp3
-/
/-
invalid occurrence of recursive arg#7 of 'lang.time.transform_expr.compose', the body of the functional type depends on it.
All Messages (28)

PROBLEM WITH TRANSFORM EXPRESSIONS
-/
inductive transform_expr' {K : Type u} [field K] [inhabited K] 
  --{f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2:=sp1 : spc K f2) 
 -- (sp1 : Σf1 : fm K TIME, spc K f1)  (sp2 : Σf2 : fm K TIME, spc K f2 := sp1)
  : Π {f1 : fm K TIME} (sp1 : spc K f1), Π {f2 : fm K TIME} (sp2 : spc K f2), Type u
| lit {f1 : fm K TIME} (sp1 : spc K f1) {f2 : fm K TIME} (sp2 : spc K f2) (p : time_transform sp1 sp2) : transform_expr' sp1 sp2
| var (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2) (v : transform_var sp1.2 sp2.2) : transform_expr' sp1.2 sp2.2
| apply_duration (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2) (v : transform_expr' sp1.2 sp2.2) (d : duration_expr1.2) : transform_expr' sp1.2 sp2.2
| compose (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2)  (v : transform_expr' sp1.2 sp2.2) 
  (sp3 : Σf3 : fm K TIME, spc K f3)  (v : transform_expr' sp2.2 sp3.2) : transform_expr' sp1.2 sp3.2

/-
invalid occurrence of recursive arg#7 of 'lang.time.transform_expr.compose', the body of the functional type depends on it.
All Messages (28)
-/
inductive transform_expr {K : Type u} [field K] [inhabited K] 
  --{f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2:=sp1 : spc K f2) 
 -- (sp1 : Σf1 : fm K TIME, spc K f1)  (sp2 : Σf2 : fm K TIME, spc K f2 := sp1)
  : Π {f1 : fm K TIME} (sp1 : spc K f1), Π {f2 : fm K TIME} (sp2 : spc K f2), Type u
| lit {f1 : fm K TIME} {sp1 : spc K f1} {f2 : fm K TIME} {sp2 : spc K f2} (p : time_transform sp1 sp2) : transform_expr sp1 sp2
| var {f1 : fm K TIME} {sp1 : spc K f1} {f2 : fm K TIME} {sp2 : spc K f2} (v : transform_var sp1 sp2) : transform_expr sp1 sp2
| apply_duration {f1 : fm K TIME} {sp1 : spc K f1} {f2 : fm K TIME} {sp2 : spc K f2} (v : transform_expr sp1 sp2) (d : duration_expr1) : transform_expr sp1 sp2
| compose_lit {f1 : fm K TIME} {sp1 : spc K f1} {f2 : fm K TIME} {sp2 : spc K f2} (v : time_transform sp1 sp2) 
  {f3 : fm K TIME} {sp3 : spc K f3}  (v : time_transform sp2 sp3) : transform_expr sp1 sp3

/-

inductive transform_expr {K : Type u} [field K] [inhabited K] 
  --{f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2:=sp1 : spc K f2) 
 -- (sp1 : Σf1 : fm K TIME, spc K f1)  (sp2 : Σf2 : fm K TIME, spc K f2 := sp1)
  : Σf1 : fm K TIME, spc K f1 → Σf2 : fm K TIME, spc K f2 → Type u
| lit (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2) (p : time_transform sp1.1 sp1.2) : transform_expr
--| var (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2) (v : transform_var sp1.1 sp1.2) : transform_expr sp1 sp2
--| apply_duration (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2) (v : transform_expr ) (d : duration_expr) : transform_expr sp1 sp2
--| compose (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2)  (v : transform_expr sp1 sp2) 
 -- (sp3 : Σf3 : fm K TIME, spc K f3)  (v : transform_expr sp2 sp3) : transform_expr sp1 sp3


-/

abbreviation transform_env {K : Type u} [field K] [inhabited K] 
  {f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2 : spc K f2)  := 
  transform_var sp1 sp2 → time_transform sp1 sp2

abbreviation transform_eval  {K : Type u} [field K] [inhabited K] 
  {f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2 : spc K f2) := 
  transform_env sp1 sp2 → transform_expr sp1 sp2 → time_transform sp1 sp2

/-
Overall environment

--omitting transforms from environment for now, which will make
--env.env, cmd, and etc. , even more complicated in terms of types
--TODO: Go ahead and complete the environment. Thanks! --Kevin
-/

variables {f2 : fm K TIME} (sp2 : spc K f2)

structure env {K : Type u} [field K] [inhabited K] 
  --      {f : fm K TIME} (sp : spc K f) {f2 : fm K TIME} {sp2 : spc K f2} :=
  :=
  (d : Π {f : fm K TIME}, Π (sp : spc K f), duration_env sp )
  (t : Π {f : fm K TIME}, Π (sp : spc K f), time_env sp )
  (tr : Π {f1 : fm K TIME}, Π (sp1 : spc K f1), Π {f2 : fm K TIME}, Π (sp2 : spc K f2), transform_env sp1 sp2)

#check sp.tr sp2

open time

def p : Π {f : fm K TIME}, Π (sp : spc K f), duration_env sp :=
  λf,λsp, λv,⟨mk_vectr sp 1⟩

#check p

#check transform_env
def env.init (K : Type u) [field K] [inhabited K]  : env :=
  ⟨
    (λf: fm K TIME, λsp, λv, ⟨mk_vectr sp 1⟩),
    (λf: fm K TIME, λsp, λv, ⟨mk_point sp 0⟩),
    (λf: fm K TIME, λsp1, λf2, λsp2, (λv, sp1.time_tr sp2))
  ⟩

structure eval {K : Type u} [field K] [inhabited K] :=
  (d : Π {f : fm K TIME}, Π (sp : spc K f), duration_eval sp )
  (t : Π {f : fm K TIME}, Π (sp : spc K f), time_eval sp )
  (tr : Π {f1 : fm K TIME}, Π (sp1 : spc K f1), Π {f2 : fm K TIME}, Π (sp2 : spc K f2), transform_eval sp1 sp2)

def eval.init (K : Type u) [field K] [inhabited K] : eval := 
  ⟨ 
    (λf: fm K TIME, λsp, λenv_,λexpr_, ⟨mk_vectr sp 1⟩),
    (λf: fm K TIME, λsp, λenv_,λexpr_, ⟨mk_point sp 0⟩),
    (λf: fm K TIME, λsp1, λf2, λsp2, (λenv_,λexpr_, sp1.time_tr sp2 : transform_eval sp1 sp2)),
  ⟩
end lang.time
