import .expr_base
import ...phys.geom.geom1d
import .scalar_expr


namespace lang.geom1d

universes u

structure geom1d_frame_var extends var 

inductive geom1d_frame_expr : Type 1
| lit (f : geom1d_frame) : geom1d_frame_expr
| var (v : geom1d_frame_var) : geom1d_frame_expr


abbreviation geom1d_frame_env :=
  geom1d_frame_var → geom1d_frame
abbreviation geom1d_frame_eval :=
  geom1d_frame_env → geom1d_frame_expr → geom1d_frame

noncomputable def default_frame_env : geom1d_frame_env := 
  λv, geom1d_std_frame
noncomputable def default_frame_eval : geom1d_frame_eval := λenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact (default_frame_env expr_)
  end

def static_frame_eval : geom1d_frame_eval 
| env_ (geom1d_frame_expr.lit f) := f
| env_ (geom1d_frame_expr.var v) := env_ v

noncomputable def geom1d_frame_expr.value (expr_ : geom1d_frame_expr) : geom1d_frame :=
  (static_frame_eval) (default_frame_env) expr_

structure geom1d_space_var (f : geom1d_frame_expr) extends var

inductive geom1d_space_expr (f : geom1d_frame_expr) : Type 1
| lit (sp : geom1d_space f.value) : geom1d_space_expr
| var (v : geom1d_space_var f) : geom1d_space_expr
| mk : geom1d_space_expr

abbreviation geom1d_space_env := Π(f : geom1d_frame_expr),
  geom1d_space_var f → geom1d_space f.value
abbreviation geom1d_space_eval := Π(f : geom1d_frame_expr),
  geom1d_space_env → geom1d_space_expr f → geom1d_space f.value


noncomputable def default_space_env : geom1d_space_env := 
  λf, λv, mk_space f.value
noncomputable def default_space_eval : geom1d_space_eval := λf, λenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact (default_space_env f expr_),
    exact mk_space f.value
  end

noncomputable def static_space_eval : geom1d_space_eval 
| f env_ (geom1d_space_expr.lit sp) := sp
| f env_ (geom1d_space_expr.var v) := env_ f v
| f env_ (geom1d_space_expr.mk) := mk_space f.value

noncomputable def geom1d_space_expr.value {f : geom1d_frame_expr} (expr_ : geom1d_space_expr f)  : geom1d_space f.value :=
  (static_space_eval f) (default_space_env) expr_

structure transform_var  
  {f1 : geom1d_frame_expr} (sp1 : geom1d_space_expr f1) {f2 : geom1d_frame_expr} (sp2 : geom1d_space_expr f2) extends var

inductive geom1d_transform_expr
  : Π {f1 : geom1d_frame_expr} (sp1 : geom1d_space_expr f1), Π {f2 : geom1d_frame_expr} (sp2 : geom1d_space_expr f2), Type 1
| lit {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1} {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2} (p : geom1d_transform sp1.value sp2.value) : geom1d_transform_expr sp1 sp2
| var {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1} {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2} (v : transform_var sp1 sp2) : geom1d_transform_expr sp1 sp2
| compose_lit {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1} {f2 : geom1d_frame} {sp2 : geom1d_space f2} (t1 : geom1d_transform sp1.value sp2) 
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


noncomputable def default_transform_env 
  {f1 : geom1d_frame_expr} (sp1 : geom1d_space_expr f1) {f2 : geom1d_frame_expr} (sp2 : geom1d_space_expr f2) 
    : transform_env sp1 sp2:=
    λv, (sp1.value).mk_geom1d_transform_to sp2.value

noncomputable def default_transform_eval 
  {f1 : geom1d_frame_expr} (sp1 : geom1d_space_expr f1) {f2 : geom1d_frame_expr} (sp2 : geom1d_space_expr f2) : transform_eval sp1 sp2 :=
  λenv_, λexpr_,  sp1.value.mk_geom1d_transform_to sp2.value

noncomputable def static_transform_eval 
  {f1 : geom1d_frame_expr} (sp1 : geom1d_space_expr f1) {f2 : geom1d_frame_expr} (sp2 : geom1d_space_expr f2) : transform_eval sp1 sp2 
| env_ (geom1d_transform_expr.lit tr) := tr
| env_ (geom1d_transform_expr.var v) := env_ v
| env_ (geom1d_transform_expr.compose_lit t1 t2) := ⟨⟨t1.1.1.trans t2.1.1⟩⟩
| env_ (geom1d_transform_expr.inv_lit t) := ⟨⟨(t.1.1).symm⟩⟩
| env_ expr_ := default_transform_eval sp1 sp2 (default_transform_env sp1 sp2) expr_

noncomputable def geom1d_transform_expr.value {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1} {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2}
  (expr_ : geom1d_transform_expr sp1 sp2) : geom1d_transform sp1.value sp2.value :=
  ((static_transform_eval sp1 sp2) (default_transform_env sp1 sp2) expr_)

variables {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1} {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2}
          (expr_ : geom1d_transform_expr sp1 sp2)


class transform_has_inv 
  {f1 : geom1d_frame_expr} (sp1 : geom1d_space_expr f1) {f2 : geom1d_frame_expr} (sp2 : geom1d_space_expr f2) := 
  (inv : geom1d_transform_expr sp1 sp2 → geom1d_transform_expr sp2 sp1)
notation tr⁻¹:= transform_has_inv.inv tr

noncomputable instance transform_inv {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1} {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2} 
  : transform_has_inv sp1 sp2 := ⟨λt,
    begin
      let lit := t.value,
     exact (geom1d_transform_expr.inv_lit lit),
    end⟩

noncomputable def geom1d_transform_expr.trans 
  {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1} {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2}
 {f3 : geom1d_frame_expr} {sp3 : geom1d_space_expr f3} (expr_ : geom1d_transform_expr sp1 sp2) : geom1d_transform_expr sp2 sp3 → geom1d_transform_expr sp1 sp3 
 := λt2,
 geom1d_transform_expr.compose_lit expr_.value t2.value

structure displacement1d_var {f : geom1d_frame_expr} (sp : geom1d_space_expr f) extends var 

structure position1d_var  {f : geom1d_frame_expr} (sp : geom1d_space_expr f) extends var
set_option trace.app_builder true --need to fix real_scalar for this to work

mutual inductive displacement1d_expr, position1d_expr {f : geom1d_frame_expr} (sp : geom1d_space_expr f)
with displacement1d_expr : Type 1
| zero : displacement1d_expr
| one : displacement1d_expr 
| lit (v : displacement1d sp.value) : displacement1d_expr
| var (v : displacement1d_var sp) : displacement1d_expr
| add_displacement1d_displacement1d (d1 : displacement1d_expr) (d2 : displacement1d_expr) : displacement1d_expr
| neg_displacement1d (d : displacement1d_expr) : displacement1d_expr
| sub_displacement1d_displacement1d (d1 : displacement1d_expr) (d2 : displacement1d_expr) : displacement1d_expr
| sub_position1d_position1d (t1 : position1d_expr) (t2 : position1d_expr) : displacement1d_expr
| smul_displacement1d (k : real_scalar_expr) (d : displacement1d_expr) : displacement1d_expr
| apply_displacement1d_lit {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2} (v : geom1d_transform_expr sp2 sp) 
    (d : displacement1d sp2.value) : displacement1d_expr
with position1d_expr : Type 1
| lit (p : position1d sp.value) : position1d_expr
| var (v : position1d_var sp) : position1d_expr
| add_displacement1d_position1d (d : displacement1d_expr) (t : position1d_expr) : position1d_expr
| apply_position1d_lit {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2} (v : geom1d_transform_expr sp2 sp) 
    (t : position1d sp2.value) : position1d_expr


abbreviation displacement1d_env {f : geom1d_frame_expr} (sp : geom1d_space_expr f) := 
  displacement1d_var sp → displacement1d sp.value

attribute [elab_as_eliminator] 
abbreviation position1d_env {f : geom1d_frame_expr} (sp : geom1d_space_expr f) :=
  position1d_var sp → position1d sp.value

abbreviation displacement1d_eval := Π{f : geom1d_frame_expr} (sp : geom1d_space_expr f),
  position1d_env sp → displacement1d_env sp → displacement1d_expr sp → displacement1d sp.value

abbreviation position1d_eval := Π{f : geom1d_frame_expr} (sp : geom1d_space_expr f), 
  position1d_env sp → displacement1d_env sp → position1d_expr sp → position1d sp.value

noncomputable def default_displacement1d_env {f : geom1d_frame_expr} (sp : geom1d_space_expr f) : displacement1d_env sp := λv, (mk_displacement1d sp.value 1)
noncomputable def default_displacement1d_eval : displacement1d_eval  
  := λf sp, λtenv_, λdenv_, λexpr_, 
  begin
    repeat {exact (mk_displacement1d sp.value 1)}
  end

noncomputable def default_position1d_env {f : geom1d_frame_expr} (sp : geom1d_space_expr f) : position1d_env sp 
  := (λv, (mk_position1d sp.value 1))

set_option eqn_compiler.max_steps 8192
noncomputable mutual def static_displacement1d_eval, static_position1d_eval 
with static_displacement1d_eval : displacement1d_eval 
| f sp tenv_ denv_ (displacement1d_expr.zero) := 0
| f sp tenv_ denv_ (displacement1d_expr.one) := mk_displacement1d sp.value 1
| f sp tenv_ denv_ (displacement1d_expr.lit d) := d
| f sp tenv_ denv_ (displacement1d_expr.var v) := denv_ v
| f sp tenv_ denv_ (displacement1d_expr.add_displacement1d_displacement1d d1 d2) := (static_displacement1d_eval sp tenv_ denv_ d1) +ᵥ (static_displacement1d_eval sp tenv_ denv_ d2)
| f sp tenv_ denv_ (displacement1d_expr.neg_displacement1d d) := -(static_displacement1d_eval sp tenv_ denv_ d)
| f sp tenv_ denv_ (displacement1d_expr.sub_displacement1d_displacement1d d1 d2) := (static_displacement1d_eval sp tenv_ denv_ d1) -ᵥ (static_displacement1d_eval sp tenv_ denv_ d2)
| f sp tenv_ denv_ (displacement1d_expr.sub_position1d_position1d t1 t2) := (static_position1d_eval sp tenv_ denv_ t1) -ᵥ (static_position1d_eval sp tenv_ denv_ t2)
| f sp tenv_ denv_ (displacement1d_expr.smul_displacement1d s d) := (static_real_scalar_eval default_real_scalar_env s)•(static_displacement1d_eval sp tenv_ denv_ d)
| f sp tenv_ denv_ (displacement1d_expr.apply_displacement1d_lit t d) := t.value.transform_displacement1d d
with static_position1d_eval : position1d_eval
| f sp tenv_ denv_ (position1d_expr.lit p) := p
| f sp tenv_ denv_ (position1d_expr.var v) := tenv_ v
| f sp tenv_ denv_ (position1d_expr.add_displacement1d_position1d d t) := (static_displacement1d_eval sp tenv_ denv_ d) +ᵥ (static_position1d_eval sp tenv_ denv_ t)
| f sp tenv_ denv_ (position1d_expr.apply_position1d_lit tr t) := tr.value.transform_position1d t


noncomputable def default_position1d_eval : position1d_eval := λf sp, λtenv_, λdenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact default_position1d_env sp expr_,
    repeat {exact (mk_position1d sp.value 1)}
  end

noncomputable def position1d_expr.value {f : geom1d_frame_expr} {sp : geom1d_space_expr f} (expr_ : position1d_expr sp) : position1d sp.value :=
  (static_position1d_eval sp) (default_position1d_env sp) (default_displacement1d_env sp) expr_

noncomputable def displacement1d_expr.value {f : geom1d_frame_expr} {sp : geom1d_space_expr f} (expr_ : displacement1d_expr sp) : displacement1d sp.value :=
  (static_displacement1d_eval sp) (default_position1d_env sp) (default_displacement1d_env sp) expr_

class position1d_has_lit {f : geom1d_frame_expr} (sp : geom1d_space_expr f) := 
  (cast : position1d sp.value → position1d_expr sp)
notation `|`tlit`|` := position1d_has_lit.cast tlit

instance position1d_lit {f : geom1d_frame_expr} (sp : geom1d_space_expr f) : position1d_has_lit  sp := 
  ⟨λt : position1d sp.value, position1d_expr.lit t⟩

class displacement1d_has_lit {f : geom1d_frame_expr} (sp : geom1d_space_expr f) := 
  (cast : displacement1d sp.value → displacement1d_expr sp)
notation `|`tlit`|` := displacement1d_has_lit.cast tlit

instance displacement1d_lit {f : geom1d_frame_expr} (sp : geom1d_space_expr f) : displacement1d_has_lit  sp := 
  ⟨λt : displacement1d sp.value, displacement1d_expr.lit t⟩

class position1d_frame_has_lit := 
  (cast : geom1d_frame → geom1d_frame_expr)
notation `|`flit`|` := position1d_frame_has_lit.cast flit

instance position1d_frame_lit : position1d_frame_has_lit := 
  ⟨λf, geom1d_frame_expr.lit f⟩

class position1d_space_has_lit (f : geom1d_frame_expr ) := 
  (cast : geom1d_space f.value  → geom1d_space_expr f)
notation `|`slit`|` := position1d_space_has_lit.cast slit

instance position1d_space_lit {f : geom1d_frame_expr} : position1d_space_has_lit f := 
  ⟨λs, geom1d_space_expr.lit s⟩


variables  {f : geom1d_frame_expr} {sp : geom1d_space_expr f} 

noncomputable def mk_geom1d_frame_expr {f : geom1d_frame_expr} {sp : geom1d_space_expr f} (o : position1d_expr sp) (b : displacement1d_expr sp) : geom1d_frame_expr :=
  |(mk_geom1d_frame o.value b.value)|

def mk_geom1d_space_expr (f : geom1d_frame_expr) : geom1d_space_expr f :=
  geom1d_space_expr.mk


instance has_one_displacement1d_expr : has_one (displacement1d_expr sp) := ⟨displacement1d_expr.one⟩
instance has_add_displacement1d_expr : has_add (displacement1d_expr sp) := ⟨λ v1 v2, displacement1d_expr.add_displacement1d_displacement1d v1 v2 ⟩
instance has_zero_displacement1d_expr : has_zero (displacement1d_expr sp) := ⟨displacement1d_expr.zero⟩

instance has_neg_displacement1d_expr : has_neg (displacement1d_expr sp) := ⟨λv1, displacement1d_expr.neg_displacement1d v1⟩
instance has_sub_displacement1d_expr : has_sub (displacement1d_expr sp) := ⟨λ v1 v2, displacement1d_expr.sub_displacement1d_displacement1d v1 v2⟩ 

instance : has_vadd (displacement1d_expr sp) (position1d_expr sp) := ⟨λv p, position1d_expr.add_displacement1d_position1d v p⟩
instance : has_vsub (displacement1d_expr sp) (position1d_expr sp) := ⟨λt1 t2, displacement1d_expr.sub_position1d_position1d t1 t2⟩


notation t+ᵥv := has_vadd.vadd v t
notation k•d :=  displacement1d_expr.smul_displacement1d k d
notation d•k :=  displacement1d_expr.smul_displacement1d k d
notation tr⬝d := displacement1d_expr.apply_displacement1dation_lit tr d
notation tr⬝t := position1d_expr.apply_position1d_lit tr t
notation tr∘tr := geom1d_transform_expr.compose_lit tr tr

class geom1d_transform_has_complit 
  {f1 : geom1d_frame_expr} (sp1 : geom1d_space_expr f1) 
  {f2 : geom1d_frame_expr} (sp2 : geom1d_space_expr f2)
  {f3 : geom1d_frame_expr} (sp3 : geom1d_space_expr f3)  
  := 
  (cast : 
    geom1d_transform sp1.value sp2.value → 
    geom1d_transform sp2.value sp3.value →
    geom1d_transform_expr sp1 sp3)
notation tr1`∘`tr2 := geom1d_transform_has_complit.cast tr1 tr2
noncomputable instance g1dcomplit
  {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1} 
  {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2}
  {f3 : geom1d_frame_expr} {sp3 : geom1d_space_expr f3} : geom1d_transform_has_complit sp1 sp2 sp3 := 
    ⟨λt1 t2, geom1d_transform_expr.compose_lit t1 t2⟩ 


class geom1d_transform_has_comp 
  {f1 : geom1d_frame_expr} (sp1 : geom1d_space_expr f1) 
  {f2 : geom1d_frame_expr} (sp2 : geom1d_space_expr f2)
  {f3 : geom1d_frame_expr} (sp3 : geom1d_space_expr f3)  
  := 
  (cast : 
    geom1d_transform_expr sp1 sp2 → 
    geom1d_transform_expr sp2 sp3 →
    geom1d_transform_expr sp1 sp3)
notation tr1`∘`tr2 := geom1d_transform_has_comp.cast tr1 tr2
instance g1dcomp
  {f1 : geom1d_frame_expr} {sp1 : geom1d_space_expr f1} 
  {f2 : geom1d_frame_expr} {sp2 : geom1d_space_expr f2}
  {f3 : geom1d_frame_expr} {sp3 : geom1d_space_expr f3} : geom1d_transform_has_comp sp1 sp2 sp3 := 
    ⟨λt1 t2, geom1d_transform_expr.compose t1 t2⟩ 

end lang.geom1d
