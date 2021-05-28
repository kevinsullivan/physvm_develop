import .expr_base
import ...phys.geom.geom1d
import .scalar_expr


namespace lang.geom1d

universes u

--@[protected]
--abbreviation scalar := ℚ



structure geom1d_frame_var extends var 


inductive geom1d_frame_expr : Type 1 --{f : fm scalar T}
| lit (f : fm scalar LENGTH) : geom1d_frame_expr
| var (v : geom1d_frame_var) : geom1d_frame_expr


abbreviation geom1d_frame_env :=
  geom1d_frame_var → fm scalar LENGTH
abbreviation geom1d_frame_eval :=
  geom1d_frame_env → geom1d_frame_expr → fm scalar LENGTH

def default_frame_env : geom1d_frame_env := 
  λv, geom1d_std_frame
def default_frame_eval : geom1d_frame_eval := λenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact (default_frame_env expr_)
  end

def static_frame_eval : geom1d_frame_eval 
| env_ (geom1d_frame_expr.lit f) := f
| env_ (geom1d_frame_expr.var v) := env_ v

def geom1d_frame_expr.value (expr_ : geom1d_frame_expr) : fm scalar LENGTH :=
  (static_frame_eval) (default_frame_env) expr_

structure geom1d_space_var (f : geom1d_frame_expr) extends var

inductive geom1d_space_expr (f : geom1d_frame_expr) : Type 1
| lit (sp : spc scalar f.value) : geom1d_space_expr
| var (v : geom1d_space_var f) : geom1d_space_expr
| mk : geom1d_space_expr

abbreviation geom1d_space_env := Π(f : geom1d_frame_expr),
  geom1d_space_var f → spc scalar f.value
abbreviation geom1d_space_eval := Π(f : geom1d_frame_expr),
  geom1d_space_env → geom1d_space_expr f → spc scalar f.value


def default_space_env : geom1d_space_env := 
  λf, λv, mk_space scalar f.value
def default_space_eval : geom1d_space_eval := λf, λenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact (default_space_env f expr_),
    exact mk_space scalar f.value
  end

def static_space_eval : geom1d_space_eval 
| f env_ (geom1d_space_expr.lit sp) := sp
| f env_ (geom1d_space_expr.var v) := env_ f v
| f env_ (geom1d_space_expr.mk) := mk_space scalar f.value

def geom1d_space_expr.value {f : geom1d_frame_expr} (expr_ : geom1d_space_expr f)  : spc scalar f.value :=
  (static_space_eval f) (default_space_env) expr_

/-
Transform
-/
structure transform_var  
  {f1 : geom1d_frame_expr} (sp1 : geom1d_space_expr f1) {f2 : geom1d_frame_expr} (sp2 : geom1d_space_expr f2) extends var

inductive geom1d_transform_expr
  --{f1 : fm scalar LENGTH} {f2 : fm scalar LENGTH} (sp1 : spc scalar f1) (sp2:=sp1 : spc scalar f2) 
 -- (sp1 : Σf1 : fm scalar LENGTH, spc scalar f1)  (sp2 : Σf2 : fm scalar LENGTH, spc scalar f2 := sp1)
  : Π {f1 : geom1d_frame_expr} (sp1 : geom1d_space_expr f1), Π {f2 : geom1d_frame_expr} (sp2 : geom1d_space_expr f2), Type 1
| lit {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1} {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2} (p : geom1d_transform sp1.value sp2.value) : geom1d_transform_expr sp1 sp2
| var {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1} {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2} (v : transform_var sp1 sp2) : geom1d_transform_expr sp1 sp2
| compose_lit {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1} {f2 : fm scalar LENGTH} {sp2 : spc scalar f2} (t1 : geom1d_transform sp1.value sp2) 
  {f3 : geom1d_frame_expr} {sp3 : geom1d_space_expr f3}  (t2 : geom1d_transform sp2 sp3.value) : geom1d_transform_expr sp1 sp3
| inv_lit {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1} {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2} (t : geom1d_transform sp2.value sp1.value) : geom1d_transform_expr sp1 sp2
| compose 
  {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1}
  {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2}
  {f3 : geom1d_frame_expr} {sp3 : geom1d_space_expr f3}
  (t1 : geom1d_transform_expr sp1 sp3) (t2 : geom1d_transform_expr sp3 sp2) : geom1d_transform_expr sp1 sp2
| inv
  {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1}
  {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2}
  (tr : geom1d_transform_expr sp2 sp1) : geom1d_transform_expr sp1 sp2

class geom1d_transform_has_lit 
  {f1 : geom1d_frame_expr} (sp1 : geom1d_space_expr f1) {f2 : geom1d_frame_expr} (sp2 : geom1d_space_expr f2) := 
  (cast : geom1d_transform sp1.value sp2.value → geom1d_transform_expr sp1 sp2)
notation `|`tlit`|` := geom1d_transform_has_lit.cast tlit

instance geom1d_transform_lit 
  {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1} {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2} : geom1d_transform_has_lit sp1 sp2 := 
  ⟨λt, geom1d_transform_expr.lit t⟩

abbreviation transform_env 
  {f1 : geom1d_frame_expr} (sp1 : geom1d_space_expr f1) {f2 : geom1d_frame_expr} (sp2 : geom1d_space_expr f2)  := 
  transform_var sp1 sp2 → geom1d_transform sp1.value sp2.value

abbreviation transform_eval 
  {f1 : geom1d_frame_expr} (sp1 : geom1d_space_expr f1) {f2 : geom1d_frame_expr} (sp2 : geom1d_space_expr f2) := 
  transform_env sp1 sp2 → geom1d_transform_expr sp1 sp2 → geom1d_transform sp1.value sp2.value


def default_transform_env 
  {f1 : geom1d_frame_expr} (sp1 : geom1d_space_expr f1) {f2 : geom1d_frame_expr} (sp2 : geom1d_space_expr f2) : transform_env sp1 sp2:=
    λv, sp1.value.mk_geom1d_transform_to sp2.value

def default_transform_eval 
  {f1 : geom1d_frame_expr} (sp1 : geom1d_space_expr f1) {f2 : geom1d_frame_expr} (sp2 : geom1d_space_expr f2) : transform_eval sp1 sp2 :=
  λenv_, λexpr_,  sp1.value.mk_geom1d_transform_to sp2.value

def static_transform_eval 
  {f1 : geom1d_frame_expr} (sp1 : geom1d_space_expr f1) {f2 : geom1d_frame_expr} (sp2 : geom1d_space_expr f2) : transform_eval sp1 sp2 
| env_ (geom1d_transform_expr.lit tr) := tr
| env_ (geom1d_transform_expr.var v) := env_ v
| env_ (geom1d_transform_expr.compose_lit t1 t2) := ⟨⟨t1.1.1.trans t2.1.1⟩⟩
| env_ (geom1d_transform_expr.inv_lit t) := ⟨⟨(t.1.1).symm⟩⟩
| env_ expr_ := default_transform_eval sp1 sp2 (default_transform_env sp1 sp2) expr_

def geom1d_transform_expr.value {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1} {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2}
  (expr_ : geom1d_transform_expr sp1 sp2) : geom1d_transform sp1.value sp2.value :=
  ((static_transform_eval sp1 sp2) (default_transform_env sp1 sp2) expr_)

variables {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1} {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2}
          (expr_ : geom1d_transform_expr sp1 sp2)

#check expr_.value

--INVERSE CANNOT BE DEEPLY EMBEDDED - IT HAS A DIFFERENT TYPE

/-
class transform_has_inv 
  {f1 : geom1d_frame_expr} (sp1 : geom1d_space_expr f1) {f2 : geom1d_frame_expr} (sp2 : geom1d_space_expr f2) := 
  (inv : geom1d_transform_expr sp1 sp2 → geom1d_transform_expr sp2 sp1)
notation tr⁻¹:= transform_has_inv.inv tr

instance transform_inv {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1} {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2} 
  : transform_has_inv sp1 sp2 := ⟨λt,
    begin
      let lit := t.value,
      let ftr := lit.1,
      let mtr := ftr.1.symm,
      let invlit : geom1d_transform sp2.value sp1.value := ⟨⟨mtr⟩⟩,
      exact [invlit]
    end
-/
class transform_has_inv 
  {f1 : geom1d_frame_expr} (sp1 : geom1d_space_expr f1) {f2 : geom1d_frame_expr} (sp2 : geom1d_space_expr f2) := 
  (inv : geom1d_transform_expr sp1 sp2 → geom1d_transform_expr sp2 sp1)
notation tr⁻¹:= transform_has_inv.inv tr

instance transform_inv {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1} {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2} 
  : transform_has_inv sp1 sp2 := ⟨λt,
    begin
      let lit := t.value,
     -- let ftr := lit.1,
     -- let mtr := ftr.1.symm,
     -- let invlit : geom1d_transform sp2.value sp1.value := ⟨⟨mtr⟩⟩,
     exact (geom1d_transform_expr.inv_lit lit),
    end⟩


def geom1d_transform_expr.trans 
  {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1} {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2}
 {f3 : geom1d_frame_expr} {sp3 : geom1d_space_expr f3} (expr_ : geom1d_transform_expr sp1 sp2) : geom1d_transform_expr sp2 sp3 → geom1d_transform_expr sp1 sp3 
 := λt2,
 geom1d_transform_expr.compose_lit expr_.value t2.value

structure scalar_var extends var

inductive scalar_expr : Type
| lit (s : scalar) : scalar_expr
| var (v : scalar_var) : scalar_expr
| add_scalar_scalar (s1 : scalar_expr) (s2 : scalar_expr) : scalar_expr
| mul_scalar_scalar (s1 : scalar_expr) (s2 : scalar_expr) : scalar_expr

abbreviation scalar_env := scalar_var → scalar

abbreviation scalar_eval := 
  scalar_env  → scalar_expr → scalar


def default_scalar_env 
   : scalar_env :=
    λv, 1

def default_scalar_eval 
  : scalar_eval :=
  λenv_, λexpr_,  1

def static_scalar_eval 
   : scalar_eval
| env_ (scalar_expr.lit s) := s
| env_ (scalar_expr.var v) := (env_ v)
| env_ (scalar_expr.add_scalar_scalar s1 s2) := (static_scalar_eval env_ s1) + (static_scalar_eval env_ s2)
| env_ (scalar_expr.mul_scalar_scalar s1 s2) := (static_scalar_eval env_ s1) * (static_scalar_eval env_ s2)

def position_scalar_expr.value
  (expr_ : scalar_expr) : scalar :=
  static_scalar_eval default_scalar_env expr_

instance : field scalar_expr := sorry


--class scalar_has_lit (sp : scalar_expr) := 
--  (cast : scalar → scalar_expr)
notation `|`slit`|` := scalar_expr.lit slit --scalar_has_lit.cast slit

--instance scalar_lit (sp : scalar_expr) : scalar_has_lit  sp := 
--  ⟨λt : scalar, scalar_expr.lit t⟩
/-
Duration
-/
structure displacement_var {f : geom1d_frame_expr} (sp : geom1d_space_expr f) extends var 

/-
Time
-/
structure position_var  {f : geom1d_frame_expr} (sp : geom1d_space_expr f) extends var
set_option trace.app_builder true --need to fix scalar for this to work

mutual inductive displacement_expr, position_expr {f : geom1d_frame_expr} (sp : geom1d_space_expr f)
with displacement_expr : Type 1
| zero : displacement_expr
| one : displacement_expr 
| lit (v : displacement sp.value) : displacement_expr
| var (v : displacement_var sp) : displacement_expr
| add_dur_dur (d1 : displacement_expr) (d2 : displacement_expr) : displacement_expr
| neg_dur (d : displacement_expr) : displacement_expr
| sub_dur_dur (d1 : displacement_expr) (d2 : displacement_expr) : displacement_expr
| sub_position_position (t1 : position_expr) (t2 : position_expr) : displacement_expr
| smul_dur (k : scalar_expr) (d : displacement_expr) : displacement_expr
| apply_displacement_lit {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2} (v : geom1d_transform_expr sp2 sp) 
    (d : displacement sp2.value) : displacement_expr
with position_expr : Type 1
| lit (p : position sp.value) : position_expr
| var (v : position_var sp) : position_expr
| add_dur_position (d : displacement_expr) (t : position_expr) : position_expr
| apply_position_lit {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2} (v : geom1d_transform_expr sp2 sp) 
    (t : position sp2.value) : position_expr


abbreviation displacement_env {f : geom1d_frame_expr} (sp : geom1d_space_expr f) := 
  displacement_var sp → displacement sp.value

attribute [elab_as_eliminator] 
abbreviation position_env {f : geom1d_frame_expr} (sp : geom1d_space_expr f) :=
  position_var sp → position sp.value

abbreviation displacement_eval := Π{f : geom1d_frame_expr} (sp : geom1d_space_expr f),
  position_env sp → displacement_env sp → displacement_expr sp → displacement sp.value

abbreviation position_eval := Π{f : geom1d_frame_expr} (sp : geom1d_space_expr f), 
  position_env sp → displacement_env sp → position_expr sp → position sp.value

def default_displacement_env {f : geom1d_frame_expr} (sp : geom1d_space_expr f) : displacement_env sp := λv, (mk_displacement sp.value 1)
def default_displacement_eval : displacement_eval  
  := λf sp, λtenv_, λdenv_, λexpr_, 
  begin
    --cases expr_,
    --exact expr_,
    --exact default_displacement_env sp expr_,
    repeat {exact (mk_displacement sp.value 1)}
  end

--this needs to get fixed, perhaps eval should not depend on env but use a global one *shrug*
--OR, a point evaluator needs to depend on a vector environment, and vice versa? may be acceptable
def default_position_env {f : geom1d_frame_expr} (sp : geom1d_space_expr f) : position_env sp 
  := (λv, (mk_position sp.value 1))


set_option eqn_compiler.max_steps 8192
mutual def static_displacement_eval, static_position_eval 
with static_displacement_eval : displacement_eval 
| f sp tenv_ denv_ (displacement_expr.zero) := 0
| f sp tenv_ denv_ (displacement_expr.one) := mk_displacement sp.value 1
| f sp tenv_ denv_ (displacement_expr.lit d) := d
| f sp tenv_ denv_ (displacement_expr.var v) := denv_ v
| f sp tenv_ denv_ (displacement_expr.add_dur_dur d1 d2) := (static_displacement_eval sp tenv_ denv_ d1) +ᵥ (static_displacement_eval sp tenv_ denv_ d2)
| f sp tenv_ denv_ (displacement_expr.neg_dur d) := -(static_displacement_eval sp tenv_ denv_ d)
| f sp tenv_ denv_ (displacement_expr.sub_dur_dur d1 d2) := (static_displacement_eval sp tenv_ denv_ d1) -ᵥ (static_displacement_eval sp tenv_ denv_ d2)
| f sp tenv_ denv_ (displacement_expr.sub_position_position t1 t2) := (static_position_eval sp tenv_ denv_ t1) -ᵥ (static_position_eval sp tenv_ denv_ t2)
| f sp tenv_ denv_ (displacement_expr.smul_dur s d) := (static_scalar_eval default_scalar_env s)•(static_displacement_eval sp tenv_ denv_ d)
| f sp tenv_ denv_ (displacement_expr.apply_displacement_lit t d) := t.value.transform_displacement d
with static_position_eval : position_eval
| f sp tenv_ denv_ (position_expr.lit p) := p
| f sp tenv_ denv_ (position_expr.var v) := tenv_ v
| f sp tenv_ denv_ (position_expr.add_dur_position d t) := (static_displacement_eval sp tenv_ denv_ d) +ᵥ (static_position_eval sp tenv_ denv_ t)
| f sp tenv_ denv_ (position_expr.apply_position_lit tr t) := tr.value.transform_position t


def default_position_eval : position_eval := λf sp, λtenv_, λdenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact default_position_env sp expr_,
    repeat {exact (mk_position sp.value 1)}
  end

#check position_env
#check default_position_env

def position_expr.value {f : geom1d_frame_expr} {sp : geom1d_space_expr f} (expr_ : position_expr sp) : position sp.value :=
  (static_position_eval sp) (default_position_env sp) (default_displacement_env sp) expr_

def displacement_expr.value {f : geom1d_frame_expr} {sp : geom1d_space_expr f} (expr_ : displacement_expr sp) : displacement sp.value :=
  (static_displacement_eval sp) (default_position_env sp) (default_displacement_env sp) expr_


--not working -- lean doesn't play nice with notation and dependent types
--notation `|`flit`|` := geom1d_frame_expr.lit flit
--notation `|`slit`|` := geom1d_space_expr.lit slit
--instance {scalar : Type u} [field scalar] [inhabited scalar] {f : fm scalar LENGTH} {sp : spc scalar f} : has_coe (position sp) (position_expr sp) := ⟨λt, position_expr.lit t⟩
--instance {scalar : Type u} [field scalar] [inhabited scalar] {f : fm scalar LENGTH} {sp : spc scalar f} : has_coe (displacement sp) (displacement_expr sp) := ⟨λt, displacement_expr.lit t⟩
--instance {scalar : Type u} [field scalar] [inhabited scalar] : has_coe (fm scalar LENGTH) (geom1d_frame_expr scalar) := ⟨λf, geom1d_frame_expr.lit f⟩
--instance {scalar : Type u} [field scalar] [inhabited scalar] {f : fm scalar LENGTH} : has_coe (spc scalar f) (geom1d_space_expr scalar) := ⟨λs, geom1d_space_expr.lit s⟩

/-
class has_lit (t1 : Type 0) (t2 : Type 1) :=
  (cast : t1 → t2)
notation `|`lit`|` := has_lit.cast lit
instance position_lit {f : geom1d_frame_expr} {sp : geom1d_space_expr f } : has_lit (position sp.value) (position_expr sp) :=
  ⟨λt, position_expr.lit t⟩
instance displacement_lit {f : geom1d_frame_expr} {sp : geom1d_space_expr f } : has_lit (displacement sp.value) (displacement_expr sp) :=
  ⟨λd, displacement_expr.lit d⟩
instance position_space_lit {f : geom1d_frame_expr} : has_lit (spc scalar f.value) (geom1d_space_expr f) :=
  ⟨λs, geom1d_space_expr.lit s⟩
instance position_frame_lit : has_lit (fm scalar LENGTH) (geom1d_frame_expr) :=
  ⟨λf, geom1d_frame_expr.lit f⟩
-/

class position_has_lit {f : geom1d_frame_expr} (sp : geom1d_space_expr f) := 
  (cast : position sp.value → position_expr sp)
notation `|`tlit`|` := position_has_lit.cast tlit

instance position_lit {f : geom1d_frame_expr} (sp : geom1d_space_expr f) : position_has_lit  sp := 
  ⟨λt : position sp.value, position_expr.lit t⟩

class displacement_has_lit {f : geom1d_frame_expr} (sp : geom1d_space_expr f) := 
  (cast : displacement sp.value → displacement_expr sp)
notation `|`tlit`|` := displacement_has_lit.cast tlit

instance displacement_lit {f : geom1d_frame_expr} (sp : geom1d_space_expr f) : displacement_has_lit  sp := 
  ⟨λt : displacement sp.value, displacement_expr.lit t⟩

class position_frame_has_lit := 
  (cast : fm scalar LENGTH → geom1d_frame_expr)
notation `|`flit`|` := position_frame_has_lit.cast flit

instance position_frame_lit : position_frame_has_lit := 
  ⟨λf, geom1d_frame_expr.lit f⟩

class position_space_has_lit (f : geom1d_frame_expr ) := 
  (cast : spc scalar f.value  → geom1d_space_expr f)
notation `|`slit`|` := position_space_has_lit.cast slit

instance position_space_lit {f : geom1d_frame_expr} : position_space_has_lit f := 
  ⟨λs, geom1d_space_expr.lit s⟩


variables  {f : geom1d_frame_expr} {sp : geom1d_space_expr f} 


/-
Analogous methods provided at math layer
-/
#check mk_frame

#check mk_frame
def mk_geom1d_frame_expr {f : geom1d_frame_expr} {sp : geom1d_space_expr f} (o : position_expr sp) (b : displacement_expr sp) : geom1d_frame_expr :=
  [(mk_frame o.value.to_point b.value.to_vectr)]
/-
4/7
WRITE THIS FUNCTION LATER. 
YOU NEED TO GET THE VALUE OUT OF THE f PARAMETER TO INCLUDE IT IN THE TYPE
AND THEN USE IT IN THE CONSTRUCTOR
-/
#check mk_space 
def mk_geom1d_space_expr (f : geom1d_frame_expr) : geom1d_space_expr f :=
  geom1d_space_expr.mk



def add_dur_expr_dur_expr (v1 v2 : displacement_expr sp) : displacement_expr sp := 
  displacement_expr.add_dur_dur v1 v2

def smul_dur_expr (k : scalar_expr) (v : displacement_expr sp) : displacement_expr sp := 
    displacement_expr.smul_dur k v

def neg_dur_expr (v : displacement_expr sp) : displacement_expr sp := 
    displacement_expr.neg_dur v

def sub_dur_expr_dur_expr (v1 v2 : displacement_expr sp) : displacement_expr sp :=    -- v1-v2
    displacement_expr.sub_dur_dur v1 v2

-- See unframed file for template for proving vector_space
instance has_one_dur_expr : has_one (displacement_expr sp) := ⟨displacement_expr.one⟩

instance has_add_dur_expr : has_add (displacement_expr sp) := ⟨ add_dur_expr_dur_expr ⟩

/-
THIS IS UNPROVABLE
-/
lemma add_assoc_dur_expr : ∀ a b c : displacement_expr sp, a + b + c = a + (b + c) :=
begin
    intros,
    cases a,
    { 

    },
    { 

    },
    { 

    },
    { 

    },
    { 

    },
    { 

    },
    { 

    },
    { 

    },
    { 

    },
    { 
      
    }
end

instance add_semigroup_dur_expr : add_semigroup (displacement_expr sp) := ⟨ add_dur_expr_dur_expr, add_assoc_dur_expr⟩ 

def dur_expr_zero : displacement_expr sp := displacement_expr.zero--displacement_expr.lit (mk_displacement sp.value 0)
instance has_zero_dur_expr : has_zero (displacement_expr sp) := ⟨dur_expr_zero⟩

lemma zero_add_dur_expr : ∀ a : displacement_expr sp, 0 + a = a := sorry
lemma add_zero_dur_expr : ∀ a : displacement_expr sp, a + 0 = a := sorry
instance add_monoid_dur_expr : add_monoid (displacement_expr sp) := ⟨ 
    -- add_semigroup
    add_dur_expr_dur_expr, 
    add_assoc_dur_expr, 
    -- has_zero
    dur_expr_zero,
    -- new structure 
    sorry,--@zero_add_dur_expr _ _ f sp, 
    add_zero_dur_expr
⟩

instance has_neg_dur_expr : has_neg (displacement_expr sp) := ⟨neg_dur_expr⟩
instance has_sub_dur_expr : has_sub (displacement_expr sp) := ⟨ sub_dur_expr_dur_expr⟩ 
lemma sub_eq_add_neg_dur_expr : ∀ a b : displacement_expr sp, a - b = a + -b := sorry
instance sub_neg_monoid_dur_expr : sub_neg_monoid (displacement_expr sp) := ⟨ 
    add_dur_expr_dur_expr, add_assoc_dur_expr, dur_expr_zero, 
    zero_add_dur_expr, 
    add_zero_dur_expr, -- add_monoid
    neg_dur_expr,                                                                  -- has_neg
    sub_dur_expr_dur_expr,                                                              -- has_sub
    sub_eq_add_neg_dur_expr,                                                       -- new
⟩ 

lemma add_left_neg_dur_expr : ∀ a : displacement_expr sp, -a + a = 0 := sorry
instance : add_group (displacement_expr sp) := ⟨
    -- sub_neg_monoid
    add_dur_expr_dur_expr, add_assoc_dur_expr, dur_expr_zero, zero_add_dur_expr, add_zero_dur_expr, -- add_monoid
    neg_dur_expr,                                                                  -- has_neg
    sub_dur_expr_dur_expr,                                                              -- has_sub
    sub_eq_add_neg_dur_expr, 
    -- new
    add_left_neg_dur_expr,
⟩ 

lemma add_comm_dur_expr : ∀ a b : displacement_expr sp, a + b = b + a := sorry
instance add_comm_semigroup_dur_expr : add_comm_semigroup (displacement_expr sp) := ⟨
    -- add_semigroup
    add_dur_expr_dur_expr, 
    add_assoc_dur_expr,
    add_comm_dur_expr,
⟩

instance add_comm_monoid_dur_expr : add_comm_monoid (displacement_expr sp) := ⟨
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

instance has_scalar_dur_expr : has_scalar scalar_expr (displacement_expr sp) := ⟨
smul_dur_expr,
⟩
instance : has_one scalar_expr := sorry
instance : monoid scalar_expr := sorry
instance : has_zero scalar_expr := sorry

lemma one_smul_dur_expr : ∀ b : displacement_expr sp, (1 : scalar_expr) • b = b := sorry
lemma mul_smul_dur_expr : ∀ (x y : scalar_expr) (b : displacement_expr sp), (x * y) • b = x • y • b := sorry
instance mul_action_dur_expr : mul_action scalar_expr (displacement_expr sp) := sorry /-⟨
one_smul_dur_expr,
mul_smul_dur_expr,
⟩ -/

lemma smul_add_dur_expr : ∀(r : scalar_expr) (x y : displacement_expr sp), r • (x + y) = r • x + r • y := sorry
lemma smul_zero_dur_expr : ∀(r : scalar_expr), r • (0 : displacement_expr sp) = 0 := sorry
instance distrib_mul_action_K_dur_exprKx : distrib_mul_action scalar_expr (displacement_expr sp) := ⟨
smul_add_dur_expr,
smul_zero_dur_expr,
⟩ 

-- renaming vs template due to clash with name "s" for prevailing variable
lemma add_smul_dur_expr : ∀ (a b : scalar_expr) (x : displacement_expr sp), (a + b) • x = a • x + b • x := sorry
lemma zero_smul_dur_expr : ∀ (x : displacement_expr sp), (0 : scalar_expr) • x = 0 := sorry
instance semimodule_K_displacementK : semimodule scalar_expr (displacement_expr sp) := ⟨ add_smul_dur_expr, zero_smul_dur_expr ⟩ 

instance add_comm_group_dur_expr : add_comm_group (displacement_expr sp) := ⟨
-- add_group
    add_dur_expr_dur_expr, add_assoc_dur_expr, dur_expr_zero, zero_add_dur_expr, add_zero_dur_expr, -- add_monoid
    neg_dur_expr,                                                                  -- has_neg
    sub_dur_expr_dur_expr,                                                              -- has_sub
    sub_eq_add_neg_dur_expr, 
    add_left_neg_dur_expr,
-- commutativity
    add_comm_dur_expr,
⟩


instance : vector_space scalar (displacement_expr sp) := sorry


/-
    ********************
    *** Affine space ***
    ********************
-/


/-
Affine operations
-/
instance : has_add (displacement_expr sp) := ⟨add_dur_expr_dur_expr⟩
instance : has_zero (displacement_expr sp) := ⟨dur_expr_zero⟩
instance : has_neg (displacement_expr sp) := ⟨neg_dur_expr⟩

/-
Lemmas needed to implement affine space API
-/

def sub_position_expr_position_expr {f : geom1d_frame_expr} {sp : geom1d_space_expr f}  (p1 p2 : position_expr sp) : displacement_expr sp := 
    displacement_expr.sub_position_position p1 p2
def add_position_expr_dur_expr {f : geom1d_frame_expr} {sp : geom1d_space_expr f}  (p : position_expr sp) (v : displacement_expr sp) : position_expr sp := 
    position_expr.add_dur_position v p
def add_dur_expr_position_expr {f : geom1d_frame_expr} {sp : geom1d_space_expr f}  (v : displacement_expr sp) (p : position_expr sp) : position_expr sp := 
    position_expr.add_dur_position v p

def aff_dur_expr_group_action {f : geom1d_frame_expr} {sp : geom1d_space_expr f} : displacement_expr sp → position_expr sp → position_expr sp := add_dur_expr_position_expr
instance {f : geom1d_frame_expr} {sp : geom1d_space_expr f} : has_vadd (displacement_expr sp) (position_expr sp) := ⟨λd, λt, position_expr.add_dur_position d t⟩

def spf : geom1d_space_expr [geom1d_std_frame] := [(geom1d_std_space)]

variables (d d2 : displacement_expr spf) (t : position_expr spf) (df : displacement_expr spf)

#check position_expr.add_dur_position d t

lemma zero_dur_expr_vadd'_a1 {f : geom1d_frame_expr} {sp : geom1d_space_expr f} : ∀ p : position_expr sp, (0 : displacement_expr sp) +ᵥ p = p := sorry
lemma dur_expr_add_assoc'_a1 : ∀ (g1 g2 : displacement_expr sp) (p : position_expr sp), g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p := sorry
instance dur_expr_add_action: add_action (displacement_expr sp) (position_expr sp) := 
⟨ aff_dur_expr_group_action, zero_dur_expr_vadd'_a1, dur_expr_add_assoc'_a1 ⟩ 

def aff_position_expr_group_sub : position_expr sp → position_expr sp → displacement_expr sp := sub_position_expr_position_expr
instance position_expr_has_vsub : has_vsub (displacement_expr sp) (position_expr sp) := ⟨ aff_position_expr_group_sub ⟩ 


instance : nonempty (position_expr sp) := ⟨position_expr.lit (mk_position sp.value  0)⟩

lemma position_expr_vsub_vadd_a1 : ∀ (p1 p2 : (position_expr sp)), (p1 -ᵥ p2) +ᵥ p2 = p1 := sorry
lemma position_expr_vadd_vsub_a1 : ∀ (g : displacement_expr sp) (p : position_expr sp), g +ᵥ p -ᵥ p = g := sorry
instance aff_position_expr_torsor : add_torsor (displacement_expr sp) (position_expr sp) := --affine space! 
⟨ 
    aff_dur_expr_group_action,
    zero_dur_expr_vadd'_a1,    -- add_action
    dur_expr_add_assoc'_a1,   -- add_action
    aff_position_expr_group_sub,    -- has_vsub
    position_expr_vsub_vadd_a1,     -- add_torsor
    position_expr_vadd_vsub_a1,     -- add_torsor
⟩

notation t+ᵥv := add_dur_expr_position_expr v t
notation d•k :=  smul_dur_expr k d
notation tr⬝d := displacement_expr.apply_displacement_lit tr d
notation tr⬝t := position_expr.apply_position_lit tr t

end lang.position
