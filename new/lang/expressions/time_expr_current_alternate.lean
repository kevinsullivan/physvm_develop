import .expr_base
import ...phys.time.time

namespace lang.time

universes u

section explicit

abbreviation K := ℚ



structure time_frame_var extends var 


inductive time_frame_expr : Type 1 --{f : fm K T}
| lit (f : fm K TIME) : time_frame_expr
| var (v : time_frame_var) : time_frame_expr


abbreviation time_frame_env :=
  time_frame_var → fm K TIME
abbreviation time_frame_eval :=
  time_frame_env → time_frame_expr → fm K TIME

def static_frame_env : time_frame_env := 
  λv, time_std_frame K
def static_frame_eval : time_frame_eval := λenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact (static_frame_env expr_)
  end

end explicit


section implicit

def time_frame_expr.value (expr_ : time_frame_expr) : fm K TIME :=
  (static_frame_eval) (static_frame_env) expr_

end implicit
/-
I have varying opinions on what exactly the parameters to the derived constructor should be.
-/
--| derived {f : fm K TIME} {sp : spc K f} (o : time_expr sp) (b : duration_expr sp) : time_frame_expr
section explicit



variables  (ff : time_frame_expr) 
#check ff.value 

structure time_space_var (f : time_frame_expr) extends var

inductive time_space_expr (f : time_frame_expr) : Type 1
| lit (sp : spc K f.value) : time_space_expr
| var (v : time_space_var f) : time_space_expr
| mk (f : time_frame_expr) : time_space_expr

abbreviation time_space_env := Π(f : time_frame_expr),
  time_space_var f → spc K f.value
abbreviation time_space_eval := Π(f : time_frame_expr),
  time_space_env → time_space_expr f → spc K f.value


def static_space_env : time_space_env := 
  λf, λv, mk_space K f.value
def static_space_eval : time_space_eval := λf, λenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact (static_space_env f expr_),
    exact mk_space K f.value
  end

end explicit

section implicit 

#check static_space_env
def time_space_expr.value {f : time_frame_expr} (expr_ : time_space_expr f)  : spc K f.value :=
  (static_space_eval f) (static_space_env) expr_


end implicit

/-
Duration
-/
structure duration_var {f : time_frame_expr} (sp : time_space_expr f) extends var 

/-
Time
-/
structure time_var  {f : time_frame_expr} (sp : time_space_expr f) extends var
set_option trace.app_builder true --need to fix K for this to work

mutual inductive duration_expr, time_expr {f : time_frame_expr} (sp : time_space_expr f)
with duration_expr : Type 1
| lit (v : duration sp.value) : duration_expr
| var (v : duration_var sp) : duration_expr
| add_dur_dur (d1 : duration_expr) (d2 : duration_expr) : duration_expr
| neg_dur (d : duration_expr) : duration_expr
| sub_dur_dur (d1 : duration_expr) (d2 : duration_expr) : duration_expr
| sub_time_time (t1 : time_expr) (t2 : time_expr) : duration_expr
| smul_dur (k : K) (d : duration_expr) : duration_expr
with time_expr : Type 1
| lit (p : time sp.value) : time_expr
| var (v : time_var sp) : time_expr
| add_dur_time (d : duration_expr) (t : time_expr) : time_expr


abbreviation duration_env {f : time_frame_expr} (sp : time_space_expr f) := 
  duration_var sp → duration sp.value

abbreviation duration_eval := Π{f : time_frame_expr} (sp : time_space_expr f),
  duration_env sp → duration_expr sp → duration sp.value

attribute [elab_as_eliminator] 
abbreviation time_env {f : time_frame_expr} (sp : time_space_expr f) :=
  time_var sp → time sp.value

abbreviation time_eval := Π{f : time_frame_expr} (sp : time_space_expr f), 
  time_env sp → time_expr sp → time sp.value

def static_duration_env {f : time_frame_expr} (sp : time_space_expr f) : duration_env sp := λv, (mk_duration sp.value 1)
def static_duration_eval : duration_eval  
  := λf sp, λenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact static_duration_env sp expr_,
    repeat {exact (mk_duration sp.value 1)}
  end

def static_time_env {f : time_frame_expr} (sp : time_space_expr f) : time_env sp 
  := (λv, (mk_time sp.value 1))
def static_time_eval : time_eval := λf sp, λenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact static_time_env sp expr_,
    repeat {exact (mk_time sp.value 1)}
  end

#check time_env
#check static_time_env

def time_expr.value {f : time_frame_expr} {sp : time_space_expr f} (expr_ : time_expr sp) : time sp.value :=
  (static_time_eval sp) (static_time_env sp) expr_

def duration_expr.value {f : time_frame_expr} {sp : time_space_expr f} (expr_ : duration_expr sp) : duration sp.value :=
  (static_duration_eval sp) (static_duration_env sp) expr_


--not working -- lean doesn't play nice with notation and dependent types
--notation `[`flit`]` := time_frame_expr.lit flit
--notation `[`slit`]` := time_space_expr.lit slit
--instance {K : Type u} [field K] [inhabited K] {f : fm K TIME} {sp : spc K f} : has_coe (time sp) (time_expr sp) := ⟨λt, time_expr.lit t⟩
--instance {K : Type u} [field K] [inhabited K] {f : fm K TIME} {sp : spc K f} : has_coe (duration sp) (duration_expr sp) := ⟨λt, duration_expr.lit t⟩
--instance {K : Type u} [field K] [inhabited K] : has_coe (fm K TIME) (time_frame_expr K) := ⟨λf, time_frame_expr.lit f⟩
--instance {K : Type u} [field K] [inhabited K] {f : fm K TIME} : has_coe (spc K f) (time_space_expr K) := ⟨λs, time_space_expr.lit s⟩

#check has_add

class time_has_lit {f : time_frame_expr} (sp : time_space_expr f) := 
  (cast : time sp.value → time_expr sp)
notation `[`tlit`]` := time_has_lit.cast tlit

instance time_lit {f : time_frame_expr} (sp : time_space_expr f) : time_has_lit  sp := 
  ⟨λt : time sp.value, time_expr.lit t⟩

class duration_has_lit {f : time_frame_expr} (sp : time_space_expr f) := 
  (cast : duration sp.value → duration_expr sp)
notation `[`tlit`]` := duration_has_lit.cast tlit

instance duration_lit {f : time_frame_expr} (sp : time_space_expr f) : duration_has_lit  sp := 
  ⟨λt : duration sp.value, duration_expr.lit t⟩

class time_frame_has_lit := 
  (cast : fm K TIME → time_frame_expr)
notation `[`flit`]` := time_frame_has_lit.cast flit

instance time_frame_lit : time_frame_has_lit := 
  ⟨λf, time_frame_expr.lit f⟩

class time_space_has_lit (f : time_frame_expr ) := 
  (cast : spc K f.value  → time_space_expr f)
notation `[`slit`]` := time_space_has_lit.cast slit

instance time_space_lit {f : time_frame_expr} : time_space_has_lit f := 
  ⟨λs, time_space_expr.lit s⟩


variables  {f : time_frame_expr} {sp : time_space_expr f} 


/-
Analogous methods provided at math layer
-/
#check mk_frame

#check mk_frame
def mk_time_frame_expr {f : time_frame_expr} {sp : time_space_expr f} (o : time_expr sp) (b : duration_expr sp) : time_frame_expr :=
  [(mk_frame o.value.to_point b.value.to_vectr)]
/-
4/7
WRITE THIS FUNCTION LATER. 
YOU NEED TO GET THE VALUE OUT OF THE f PARAMETER TO INCLUDE IT IN THE TYPE
AND THEN USE IT IN THE CONSTRUCTOR
-/
#check mk_space 
def mk_time_space_expr (f : time_frame_expr) : time_space_expr f :=
  time_space_expr.mk f



def add_dur_expr_dur_expr (v1 v2 : duration_expr sp) : duration_expr sp := 
  duration_expr.add_dur_dur v1 v2

def smul_dur_expr (k : K) (v : duration_expr sp) : duration_expr sp := 
    duration_expr.smul_dur k v

def neg_dur_expr (v : duration_expr sp) : duration_expr sp := 
    duration_expr.neg_dur v

def sub_dur_expr_dur_expr (v1 v2 : duration_expr sp) : duration_expr sp :=    -- v1-v2
    duration_expr.sub_dur_dur v1 v2

-- See unframed file for template for proving vector_space

instance has_add_dur_expr : has_add (duration_expr sp) := ⟨ add_dur_expr_dur_expr ⟩
lemma add_assoc_dur_expr : ∀ a b c : duration_expr sp, a + b + c = a + (b + c) := sorry
instance add_semigroup_dur_expr : add_semigroup (duration_expr sp) := ⟨ add_dur_expr_dur_expr, add_assoc_dur_expr⟩ 

def dur_expr_zero : duration_expr sp := duration_expr.lit (mk_duration sp.value 0)
instance has_zero_dur_expr : has_zero (duration_expr sp) := ⟨dur_expr_zero⟩

lemma zero_add_dur_expr : ∀ a : duration_expr sp, 0 + a = a := sorry
lemma add_zero_dur_expr : ∀ a : duration_expr sp, a + 0 = a := sorry
instance add_monoid_dur_expr : add_monoid (duration_expr sp) := ⟨ 
    -- add_semigroup
    add_dur_expr_dur_expr, 
    add_assoc_dur_expr, 
    -- has_zero
    dur_expr_zero,
    -- new structure 
    sorry,--@zero_add_dur_expr _ _ f sp, 
    add_zero_dur_expr
⟩

instance has_neg_dur_expr : has_neg (duration_expr sp) := ⟨neg_dur_expr⟩
instance has_sub_dur_expr : has_sub (duration_expr sp) := ⟨ sub_dur_expr_dur_expr⟩ 
lemma sub_eq_add_neg_dur_expr : ∀ a b : duration_expr sp, a - b = a + -b := sorry
instance sub_neg_monoid_dur_expr : sub_neg_monoid (duration_expr sp) := ⟨ 
    add_dur_expr_dur_expr, add_assoc_dur_expr, dur_expr_zero, 
    zero_add_dur_expr, 
    add_zero_dur_expr, -- add_monoid
    neg_dur_expr,                                                                  -- has_neg
    sub_dur_expr_dur_expr,                                                              -- has_sub
    sub_eq_add_neg_dur_expr,                                                       -- new
⟩ 

lemma add_left_neg_dur_expr : ∀ a : duration_expr sp, -a + a = 0 := sorry
instance : add_group (duration_expr sp) := ⟨
    -- sub_neg_monoid
    add_dur_expr_dur_expr, add_assoc_dur_expr, dur_expr_zero, zero_add_dur_expr, add_zero_dur_expr, -- add_monoid
    neg_dur_expr,                                                                  -- has_neg
    sub_dur_expr_dur_expr,                                                              -- has_sub
    sub_eq_add_neg_dur_expr, 
    -- new
    add_left_neg_dur_expr,
⟩ 

lemma add_comm_dur_expr : ∀ a b : duration_expr sp, a + b = b + a := sorry
instance add_comm_semigroup_dur_expr : add_comm_semigroup (duration_expr sp) := ⟨
    -- add_semigroup
    add_dur_expr_dur_expr, 
    add_assoc_dur_expr,
    add_comm_dur_expr,
⟩

instance add_comm_monoid_dur_expr : add_comm_monoid (duration_expr sp) := ⟨
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

instance has_scalar_dur_expr : has_scalar K (duration_expr sp) := ⟨
smul_dur_expr,
⟩

lemma one_smul_dur_expr : ∀ b : duration_expr sp, (1 : K) • b = b := sorry
lemma mul_smul_dur_expr : ∀ (x y : K) (b : duration_expr sp), (x * y) • b = x • y • b := sorry
instance mul_action_dur_expr : mul_action K (duration_expr sp) := ⟨
one_smul_dur_expr,
mul_smul_dur_expr,
⟩ 

lemma smul_add_dur_expr : ∀(r : K) (x y : duration_expr sp), r • (x + y) = r • x + r • y := sorry
lemma smul_zero_dur_expr : ∀(r : K), r • (0 : duration_expr sp) = 0 := sorry
instance distrib_mul_action_K_dur_exprKx : distrib_mul_action K (duration_expr sp) := ⟨
smul_add_dur_expr,
smul_zero_dur_expr,
⟩ 

-- renaming vs template due to clash with name "s" for prevailing variable
lemma add_smul_dur_expr : ∀ (a b : K) (x : duration_expr sp), (a + b) • x = a • x + b • x := sorry
lemma zero_smul_dur_expr : ∀ (x : duration_expr sp), (0 : K) • x = 0 := sorry
instance semimodule_K_durationK : semimodule K (duration_expr sp) := ⟨ add_smul_dur_expr, zero_smul_dur_expr ⟩ 

instance add_comm_group_dur_expr : add_comm_group (duration_expr sp) := ⟨
-- add_group
    add_dur_expr_dur_expr, add_assoc_dur_expr, dur_expr_zero, zero_add_dur_expr, add_zero_dur_expr, -- add_monoid
    neg_dur_expr,                                                                  -- has_neg
    sub_dur_expr_dur_expr,                                                              -- has_sub
    sub_eq_add_neg_dur_expr, 
    add_left_neg_dur_expr,
-- commutativity
    add_comm_dur_expr,
⟩


instance : vector_space K (duration_expr sp) := sorry


/-
    ********************
    *** Affine space ***
    ********************
-/


/-
Affine operations
-/
instance : has_add (duration_expr sp) := ⟨add_dur_expr_dur_expr⟩
instance : has_zero (duration_expr sp) := ⟨dur_expr_zero⟩
instance : has_neg (duration_expr sp) := ⟨neg_dur_expr⟩

/-
Lemmas needed to implement affine space API
-/

def sub_time_expr_time_expr {f : time_frame_expr} {sp : time_space_expr f}  (p1 p2 : time_expr sp) : duration_expr sp := 
    duration_expr.sub_time_time p1 p2
def add_time_expr_dur_expr {f : time_frame_expr} {sp : time_space_expr f}  (p : time_expr sp) (v : duration_expr sp) : time_expr sp := 
    time_expr.add_dur_time v p
def add_dur_expr_time_expr {f : time_frame_expr} {sp : time_space_expr f}  (v : duration_expr sp) (p : time_expr sp) : time_expr sp := 
    time_expr.add_dur_time v p

def aff_dur_expr_group_action {f : time_frame_expr} {sp : time_space_expr f} : duration_expr sp → time_expr sp → time_expr sp := add_dur_expr_time_expr
instance {f : time_frame_expr} {sp : time_space_expr f} : has_vadd (duration_expr sp) (time_expr sp) := ⟨λd, λt, time_expr.add_dur_time d t⟩

def spf : time_space_expr [time_std_frame K] := [(time_std_space K)]

variables (d d2 : duration_expr spf) (t : time_expr spf) (df : duration_expr spf)

#check time_expr.add_dur_time d t

lemma zero_dur_expr_vadd'_a1 {f : time_frame_expr} {sp : time_space_expr f} : ∀ p : time_expr sp, (0 : duration_expr sp) +ᵥ p = p := sorry
lemma dur_expr_add_assoc'_a1 : ∀ (g1 g2 : duration_expr sp) (p : time_expr sp), g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p := sorry
instance dur_expr_add_action: add_action (duration_expr sp) (time_expr sp) := 
⟨ aff_dur_expr_group_action, zero_dur_expr_vadd'_a1, dur_expr_add_assoc'_a1 ⟩ 

def aff_time_expr_group_sub : time_expr sp → time_expr sp → duration_expr sp := sub_time_expr_time_expr
instance time_expr_has_vsub : has_vsub (duration_expr sp) (time_expr sp) := ⟨ aff_time_expr_group_sub ⟩ 


instance : nonempty (time_expr sp) := ⟨time_expr.lit (mk_time sp.value  0)⟩

lemma time_expr_vsub_vadd_a1 : ∀ (p1 p2 : (time_expr sp)), (p1 -ᵥ p2) +ᵥ p2 = p1 := sorry
lemma time_expr_vadd_vsub_a1 : ∀ (g : duration_expr sp) (p : time_expr sp), g +ᵥ p -ᵥ p = g := sorry
instance aff_time_expr_torsor : add_torsor (duration_expr sp) (time_expr sp) := --affine space! 
⟨ 
    aff_dur_expr_group_action,
    zero_dur_expr_vadd'_a1,    -- add_action
    dur_expr_add_assoc'_a1,   -- add_action
    aff_time_expr_group_sub,    -- has_vsub
    time_expr_vsub_vadd_a1,     -- add_torsor
    time_expr_vadd_vsub_a1,     -- add_torsor
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
structure transform_var  
  {f1 : time_frame_expr} (sp1 : time_space_expr f1) {f2 : time_frame_expr} (sp2 : time_space_expr f2) extends var
/-
inductive transform_expr {K : Type u} [field K] [inhabited K] 
  --{f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2:=sp1 : spc K f2) 
 -- (sp1 : Σf1 : fm K TIME, spc K f1)  (sp2 : Σf2 : fm K TIME, spc K f2 := sp1)
  : Π {f1 : fm K TIME} (sp1 : spc K f1), Π {f2 : fm K TIME} (sp2 : spc K f2), Type u
| lit {f1 : fm K TIME} (sp1 : spc K f1) {f2 : fm K TIME} (sp2 : spc K f2) (p : time_transform sp1 sp2) : transform_expr sp1 sp2
| var (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2) (v : transform_var sp1.2 sp2.2) : transform_expr sp1 sp2
| apply_duration (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2) (v : transform_expr sp1 sp2) (d : duration_expr sp1.2) : transform_expr sp1 sp2
| compose (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2)  (v : time_transform sp1.2 sp2.2) 
  (sp3 : Σf3 : fm K TIME, spc K f3)  (v : time_transform sp1 sp2) : transform_expr sp1 sp3
-/
/-
invalid occurrence of recursive arg#7 of 'lang.time.transform_expr.compose', the body of the functional type depends on it.
All Messages (28)

PROBLEM WITH TRANSFORM EXPRESSIONS
-/
/-
inductive transform_expr' {K : Type u} [field K] [inhabited K] 
  --{f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2:=sp1 : spc K f2) 
 -- (sp1 : Σf1 : fm K TIME, spc K f1)  (sp2 : Σf2 : fm K TIME, spc K f2 := sp1)
  : Π {f1 : fm K TIME} (sp1 : spc K f1), Π {f2 : fm K TIME} (sp2 : spc K f2), Type u
| lit {f1 : fm K TIME} (sp1 : spc K f1) {f2 : fm K TIME} (sp2 : spc K f2) (p : time_transform sp1 sp2) 
    : transform_expr' sp1 sp2
| var (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2) (v : transform_var sp1.2 sp2.2) 
    : transform_expr' sp1.2 sp2.2
| apply_duration (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2) (v : transform_expr' sp1.2 sp2.2) (d : duration_expr sp1.2) 
    : transform_expr' sp1.2 sp2.2
| compose (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2)  (v : transform_expr' sp1.2 sp2.2) 
  (sp3 : Σf3 : fm K TIME, spc K f3)  (v : transform_expr' sp2.2 sp3.2) 
    : transform_expr' sp1.2 sp3.2
-/


inductive transform_expr
  --{f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2:=sp1 : spc K f2) 
 -- (sp1 : Σf1 : fm K TIME, spc K f1)  (sp2 : Σf2 : fm K TIME, spc K f2 := sp1)
  : Π {f1 : time_frame_expr} (sp1 : time_space_expr f1), Π {f2 : time_frame_expr} (sp2 : time_space_expr f2), Type 1
| lit {f1 : time_frame_expr} {sp1 : time_space_expr f1} {f2 : time_frame_expr} {sp2 : time_space_expr f2} (p : time_transform sp1.value sp2.value) : transform_expr sp1 sp2
| var {f1 : time_frame_expr} {sp1 : time_space_expr f1} {f2 : time_frame_expr} {sp2 : time_space_expr f2} (v : transform_var sp1 sp2) : transform_expr sp1 sp2
| apply_duration {f1 : time_frame_expr} {sp1 : time_space_expr f1} {f2 : time_frame_expr} {sp2 : time_space_expr f2} (v : transform_expr sp1 sp2) (d : duration_expr sp1) : transform_expr sp1 sp2
| compose_lit {f1 : time_frame_expr} {sp1 : time_space_expr f1} {f2 : fm K TIME} {sp2 : spc K f2} (v : time_transform sp1.value sp2) 
  {f3 : time_frame_expr} {sp3 : time_space_expr f3}  (v : time_transform sp2 sp3.value) : transform_expr sp1 sp3


class time_transform_has_lit 
  {f1 : time_frame_expr} (sp1 : time_space_expr f1) {f2 : time_frame_expr} (sp2 : time_space_expr f2) := 
  (cast : time_transform sp1.value sp2.value → transform_expr sp1 sp2)
notation `[`tlit`]` := time_transform_has_lit.cast tlit

instance time_transform_lit 
  {f1 : time_frame_expr} {sp1 : time_space_expr f1} {f2 : time_frame_expr} {sp2 : time_space_expr f2} : time_transform_has_lit sp1 sp2 := 
  ⟨λt, transform_expr.lit t⟩


/-

inductive transform_expr {K : Type u} [field K] [inhabited K] 
  --{f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2:=sp1 : spc K f2) 
 -- (sp1 : Σf1 : fm K TIME, spc K f1)  (sp2 : Σf2 : fm K TIME, spc K f2 := sp1)
  : Σf1 : fm K TIME, spc K f1 → Σf2 : fm K TIME, spc K f2 → Type u
| lit (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2) (p : time_transform sp1.1 sp1.2) : transform_expr
--| var (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2) (v : transform_var sp1.1 sp1.2) : transform_expr sp1 sp2
--| apply_duration (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2) (v : transform_expr ) (d : duration_expr sp) : transform_expr sp1 sp2
--| compose (sp1 : Σf1 : fm K TIME, spc K f1) (sp2 : Σf2 : fm K TIME, spc K f2)  (v : transform_expr sp1 sp2) 
 -- (sp3 : Σf3 : fm K TIME, spc K f3)  (v : transform_expr sp2 sp3) : transform_expr sp1 sp3


-/

abbreviation transform_env 
  {f1 : time_frame_expr} (sp1 : time_space_expr f1) {f2 : time_frame_expr} (sp2 : time_space_expr f2)  := 
  transform_var sp1 sp2 → time_transform sp1.value sp2.value

abbreviation transform_eval 
  {f1 : time_frame_expr} (sp1 : time_space_expr f1) {f2 : time_frame_expr} (sp2 : time_space_expr f2) := 
  transform_env sp1 sp2 → transform_expr sp1 sp2 → time_transform sp1.value sp2.value


def static_transform_env 
  {f1 : time_frame_expr} (sp1 : time_space_expr f1) {f2 : time_frame_expr} (sp2 : time_space_expr f2) : transform_env sp1 sp2:=
    λv, sp1.value.time_tr sp2.value

def static_transform_eval 
  {f1 : time_frame_expr} (sp1 : time_space_expr f1) {f2 : time_frame_expr} (sp2 : time_space_expr f2) : transform_eval sp1 sp2 :=
  λenv_, λexpr_,  sp1.value.time_tr sp2.value

def transform_expr.value {f1 : time_frame_expr} {sp1 : time_space_expr f1} {f2 : time_frame_expr} {sp2 : time_space_expr f2}
  (expr_ : transform_expr sp1 sp2) : time_transform sp1.value sp2.value :=
  ((static_transform_eval sp1 sp2) (static_transform_env sp1 sp2) expr_



--variables {f2 : fm K TIME} (sp2 : spc K f2)


--ERRORS BELOW THIS POINT DONT MATTER

structure env {K : Type u} [field K] [inhabited K] 
  --      {f : fm K TIME} (sp : spc K f) {f2 : fm K TIME} {sp2 : spc K f2} :=
  :=
  (duration : Π {f : fm K TIME}, Π (sp : spc K f), duration_env sp )
  (time : Π {f : fm K TIME}, Π (sp : spc K f), time_env sp )
  (transform : Π {f1 : fm K TIME}, Π (sp1 : spc K f1), Π {f2 : fm K TIME}, Π (sp2 : spc K f2), transform_env sp1 sp2)
  (frame : time_frame_env K)
  (space : Π (f : fm K TIME), time_space_env f)

def env.init (K : Type u) [field K] [inhabited K]  : env :=
  ⟨
    (λf: fm K TIME, λsp, λv, ⟨mk_vectr sp 1⟩),
    (λf: fm K TIME, λsp, λv, ⟨mk_point sp 0⟩),
    (λf: fm K TIME, λsp1, λf2, λsp2, (λv, sp1.time_tr sp2)),
    (λv, time_std_frame K),
    (λf, (λv, mk_space K f))
  ⟩

structure eval {K : Type u} [field K] [inhabited K] :=
  (duration : Π {f : fm K TIME}, Π (sp : spc K f), duration_eval sp )
  (time : Π {f : fm K TIME}, Π (sp : spc K f), time_eval sp )
  (transform : Π {f1 : fm K TIME}, Π (sp1 : spc K f1), Π {f2 : fm K TIME}, Π (sp2 : spc K f2), transform_eval sp1 sp2)
  (frame : time_frame_eval K)
  (space : Π (f : fm K TIME), time_space_eval f)

def eval.init (K : Type u) [field K] [inhabited K] : eval := 
  ⟨ 
    (λf: fm K TIME, λsp, λenv_,λexpr_, ⟨mk_vectr sp 1⟩),
    (λf: fm K TIME, λsp, λenv_,λexpr_, ⟨mk_point sp 0⟩),
    (λf: fm K TIME, λsp1, λf2, λsp2, (λenv_,λexpr_, sp1.time_tr sp2 : transform_eval sp1 sp2)),
    (λenv_, λexpr_, time_std_frame K),
    (λf, λenv_, λexpr_, mk_space K f)
  ⟩
end lang.time
