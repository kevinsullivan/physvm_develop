import .expr_base
import ...phys.geom.geom3d
import .scalar_expr
import ...phys.time_series.geom3d
import .time_expr


namespace lang.geom3d

universes u

structure geom3d_frame_var extends var 


inductive geom3d_frame_expr : Type 1
| lit (f : geom3d_frame) : geom3d_frame_expr
| var (v : geom3d_frame_var) : geom3d_frame_expr


abbreviation geom3d_frame_env :=
  geom3d_frame_var → geom3d_frame
abbreviation geom3d_frame_eval :=
  geom3d_frame_env → geom3d_frame_expr → geom3d_frame

noncomputable def default_frame_env : geom3d_frame_env := 
  λv, geom3d_std_frame
noncomputable def default_frame_eval : geom3d_frame_eval := λenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact (default_frame_env expr_)
  end

def static_frame_eval : geom3d_frame_eval 
| env_ (geom3d_frame_expr.lit f) := f
| env_ (geom3d_frame_expr.var v) := env_ v

noncomputable def geom3d_frame_expr.value (expr_ : geom3d_frame_expr) : geom3d_frame :=
  (static_frame_eval) (default_frame_env) expr_

structure geom3d_space_var (f : geom3d_frame_expr) extends var

inductive geom3d_space_expr (f : geom3d_frame_expr) : Type 1
| lit (sp : geom3d_space f.value) : geom3d_space_expr
| var (v : geom3d_space_var f) : geom3d_space_expr
| mk : geom3d_space_expr

abbreviation geom3d_space_env := Π(f : geom3d_frame_expr),
  geom3d_space_var f → geom3d_space f.value
abbreviation geom3d_space_eval := Π(f : geom3d_frame_expr),
  geom3d_space_env → geom3d_space_expr f → geom3d_space f.value


noncomputable def default_space_env : geom3d_space_env := 
  λf, λv, mk_space f.value
noncomputable def default_space_eval : geom3d_space_eval := λf, λenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact (default_space_env f expr_),
    exact mk_space f.value
  end

noncomputable def static_space_eval : geom3d_space_eval 
| f env_ (geom3d_space_expr.lit sp) := sp
| f env_ (geom3d_space_expr.var v) := env_ f v
| f env_ (geom3d_space_expr.mk) := mk_space f.value

noncomputable def geom3d_space_expr.value {f : geom3d_frame_expr} (expr_ : geom3d_space_expr f)  : geom3d_space f.value :=
  (static_space_eval f) (default_space_env) expr_

structure transform_var  
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) extends var

inductive geom3d_transform_expr
  : Π {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1), Π {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2), Type 1
| lit {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} (p : geom3d_transform sp1.value sp2.value) : geom3d_transform_expr sp1 sp2
| var {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} (v : transform_var sp1 sp2) : geom3d_transform_expr sp1 sp2
| compose_lit {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame} {sp2 : geom3d_space f2} (t1 : geom3d_transform sp1.value sp2) 
  {f3 : geom3d_frame_expr} {sp3 : geom3d_space_expr f3}  (t2 : geom3d_transform sp2 sp3.value) : geom3d_transform_expr sp1 sp3
| inv_lit {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} (t : geom3d_transform sp2.value sp1.value) : geom3d_transform_expr sp1 sp2
| compose 
  {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1}
  {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2}
  {f3 : geom3d_frame_expr} {sp3 : geom3d_space_expr f3}
  (t1 : geom3d_transform_expr sp1 sp3) (t2 : geom3d_transform_expr sp3 sp2) : geom3d_transform_expr sp1 sp2
| inv
  {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1}
  {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2}
  (tr : geom3d_transform_expr sp2 sp1) : geom3d_transform_expr sp1 sp2

class geom3d_transform_has_lit 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) := 
  (cast : geom3d_transform sp1.value sp2.value → geom3d_transform_expr sp1 sp2)
notation `|`tlit`|` := geom3d_transform_has_lit.cast tlit

instance geom3d_transform_lit 
  {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} : geom3d_transform_has_lit sp1 sp2 := 
  ⟨λt, geom3d_transform_expr.lit t⟩

abbreviation transform_env 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2)  := 
  transform_var sp1 sp2 → geom3d_transform sp1.value sp2.value

abbreviation transform_eval 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) := 
  transform_env sp1 sp2 → geom3d_transform_expr sp1 sp2 → geom3d_transform sp1.value sp2.value


noncomputable def default_transform_env 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) 
    : transform_env sp1 sp2:=
    λv, (sp1.value).mk_geom3d_transform_to sp2.value

noncomputable def default_transform_eval 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) : transform_eval sp1 sp2 :=
  λenv_, λexpr_,  sp1.value.mk_geom3d_transform_to sp2.value

noncomputable def static_transform_eval 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) : transform_eval sp1 sp2 
| env_ (geom3d_transform_expr.lit tr) := tr
| env_ (geom3d_transform_expr.var v) := env_ v
| env_ (geom3d_transform_expr.compose_lit t1 t2) := ⟨⟨t1.1.1.trans t2.1.1⟩⟩
| env_ (geom3d_transform_expr.inv_lit t) := ⟨⟨(t.1.1).symm⟩⟩
| env_ expr_ := default_transform_eval sp1 sp2 (default_transform_env sp1 sp2) expr_

noncomputable def geom3d_transform_expr.value {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2}
  (expr_ : geom3d_transform_expr sp1 sp2) : geom3d_transform sp1.value sp2.value :=
  ((static_transform_eval sp1 sp2) (default_transform_env sp1 sp2) expr_)

variables {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2}
          (expr_ : geom3d_transform_expr sp1 sp2)


class transform_has_inv 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) := 
  (inv : geom3d_transform_expr sp1 sp2 → geom3d_transform_expr sp2 sp1)
notation tr⁻¹:= transform_has_inv.inv tr

noncomputable instance transform_inv {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} 
  : transform_has_inv sp1 sp2 := ⟨λt,
    begin
      let lit := t.value,
     exact (geom3d_transform_expr.inv_lit lit),
    end⟩


noncomputable def geom3d_transform_expr.trans 
  {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2}
 {f3 : geom3d_frame_expr} {sp3 : geom3d_space_expr f3} (expr_ : geom3d_transform_expr sp1 sp2) : geom3d_transform_expr sp2 sp3 → geom3d_transform_expr sp1 sp3 
 := λt2,
 geom3d_transform_expr.compose_lit expr_.value t2.value


structure displacement3d_var {f : geom3d_frame_expr} (sp : geom3d_space_expr f) extends var 

structure position3d_var  {f : geom3d_frame_expr} (sp : geom3d_space_expr f) extends var

mutual inductive displacement3d_expr, position3d_expr {f : geom3d_frame_expr} (sp : geom3d_space_expr f)
with displacement3d_expr : Type 1
| zero : displacement3d_expr
| one : displacement3d_expr 
| lit (v : displacement3d sp.value) : displacement3d_expr
| var (v : displacement3d_var sp) : displacement3d_expr
| add_displacement3d_displacement3d (d1 : displacement3d_expr) (d2 : displacement3d_expr) : displacement3d_expr
| neg_displacement3d (d : displacement3d_expr) : displacement3d_expr
| sub_displacement3d_displacement3d (d1 : displacement3d_expr) (d2 : displacement3d_expr) : displacement3d_expr
| sub_position3d_position3d (t1 : position3d_expr) (t2 : position3d_expr) : displacement3d_expr
| smul_displacement3d (k : real_scalar_expr) (d : displacement3d_expr) : displacement3d_expr
| apply_displacement3d_lit {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} (v : geom3d_transform_expr sp2 sp) 
    (d : displacement3d sp2.value) : displacement3d_expr
with position3d_expr : Type 1
| lit (p : position3d sp.value) : position3d_expr
| var (v : position3d_var sp) : position3d_expr
| add_displacement3d_position3d (d : displacement3d_expr) (t : position3d_expr) : position3d_expr
| apply_position3d_lit {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} (v : geom3d_transform_expr sp2 sp) 
    (t : position3d sp2.value) : position3d_expr


abbreviation displacement3d_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) := 
  displacement3d_var sp → displacement3d sp.value

attribute [elab_as_eliminator] 
abbreviation position3d_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) :=
  position3d_var sp → position3d sp.value

abbreviation displacement3d_eval := Π{f : geom3d_frame_expr} (sp : geom3d_space_expr f),
  position3d_env sp → displacement3d_env sp → displacement3d_expr sp → displacement3d sp.value

abbreviation position3d_eval := Π{f : geom3d_frame_expr} (sp : geom3d_space_expr f), 
  position3d_env sp → displacement3d_env sp → position3d_expr sp → position3d sp.value

noncomputable def default_displacement3d_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : displacement3d_env sp := λv, (mk_displacement3d sp.value 1 1 1)
noncomputable def default_displacement3d_eval : displacement3d_eval  
  := λf sp, λtenv_, λdenv_, λexpr_, 
  begin
    repeat {exact (mk_displacement3d sp.value 1 1 1)}
  end

noncomputable def default_position3d_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : position3d_env sp 
  := (λv, (mk_position3d sp.value  1 1 1))


set_option eqn_compiler.max_steps 8192
noncomputable mutual def static_displacement3d_eval, static_position3d_eval 
with static_displacement3d_eval : displacement3d_eval 
| f sp tenv_ denv_ (displacement3d_expr.zero) := 0
| f sp tenv_ denv_ (displacement3d_expr.one) := mk_displacement3d sp.value 1 1 1
| f sp tenv_ denv_ (displacement3d_expr.lit d) := d
| f sp tenv_ denv_ (displacement3d_expr.var v) := denv_ v
| f sp tenv_ denv_ (displacement3d_expr.add_displacement3d_displacement3d d1 d2) := (static_displacement3d_eval sp tenv_ denv_ d1) +ᵥ (static_displacement3d_eval sp tenv_ denv_ d2)
| f sp tenv_ denv_ (displacement3d_expr.neg_displacement3d d) := -(static_displacement3d_eval sp tenv_ denv_ d)
| f sp tenv_ denv_ (displacement3d_expr.sub_displacement3d_displacement3d d1 d2) := (static_displacement3d_eval sp tenv_ denv_ d1) -ᵥ (static_displacement3d_eval sp tenv_ denv_ d2)
| f sp tenv_ denv_ (displacement3d_expr.sub_position3d_position3d t1 t2) := (static_position3d_eval sp tenv_ denv_ t1) -ᵥ (static_position3d_eval sp tenv_ denv_ t2)
| f sp tenv_ denv_ (displacement3d_expr.smul_displacement3d s d) := (static_real_scalar_eval default_real_scalar_env s)•(static_displacement3d_eval sp tenv_ denv_ d)
| f sp tenv_ denv_ (displacement3d_expr.apply_displacement3d_lit t d) := t.value.transform_displacement3d d
with static_position3d_eval : position3d_eval
| f sp tenv_ denv_ (position3d_expr.lit p) := p
| f sp tenv_ denv_ (position3d_expr.var v) := tenv_ v
| f sp tenv_ denv_ (position3d_expr.add_displacement3d_position3d d t) := (static_displacement3d_eval sp tenv_ denv_ d) +ᵥ (static_position3d_eval sp tenv_ denv_ t)
| f sp tenv_ denv_ (position3d_expr.apply_position3d_lit tr t) := tr.value.transform_position3d t


noncomputable def default_position3d_eval : position3d_eval := λf sp, λtenv_, λdenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact default_position3d_env sp expr_,
    repeat {exact (mk_position3d sp.value 1 1 1)}
  end

noncomputable def position3d_expr.value {f : geom3d_frame_expr} {sp : geom3d_space_expr f} (expr_ : position3d_expr sp) : position3d sp.value :=
  (static_position3d_eval sp) (default_position3d_env sp) (default_displacement3d_env sp) expr_

noncomputable def displacement3d_expr.value {f : geom3d_frame_expr} {sp : geom3d_space_expr f} (expr_ : displacement3d_expr sp) : displacement3d sp.value :=
  (static_displacement3d_eval sp) (default_position3d_env sp) (default_displacement3d_env sp) expr_


class position3d_has_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) := 
  (cast : position3d sp.value → position3d_expr sp)
notation `|`tlit`|` := position3d_has_lit.cast tlit

instance position3d_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : position3d_has_lit  sp := 
  ⟨λt : position3d sp.value, position3d_expr.lit t⟩

class displacement3d_has_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) := 
  (cast : displacement3d sp.value → displacement3d_expr sp)
notation `|`tlit`|` := displacement3d_has_lit.cast tlit

instance displacement3d_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : displacement3d_has_lit  sp := 
  ⟨λt : displacement3d sp.value, displacement3d_expr.lit t⟩

class position3d_frame_has_lit := 
  (cast : geom3d_frame → geom3d_frame_expr)
notation `|`flit`|` := position3d_frame_has_lit.cast flit

instance position3d_frame_lit : position3d_frame_has_lit := 
  ⟨λf, geom3d_frame_expr.lit f⟩

class position3d_space_has_lit (f : geom3d_frame_expr ) := 
  (cast : geom3d_space f.value  → geom3d_space_expr f)
notation `|`slit`|` := position3d_space_has_lit.cast slit

instance position3d_space_lit {f : geom3d_frame_expr} : position3d_space_has_lit f := 
  ⟨λs, geom3d_space_expr.lit s⟩


variables  {f : geom3d_frame_expr} {sp : geom3d_space_expr f} 

noncomputable def mk_geom3d_frame_expr {f : geom3d_frame_expr} {sp : geom3d_space_expr f} (o : position3d_expr sp) 
  (b0 : displacement3d_expr sp) (b1 : displacement3d_expr sp) (b2 : displacement3d_expr sp) : geom3d_frame_expr :=
  |(mk_geom3d_frame o.value b0.value b1.value b2.value)|

def mk_geom3d_space_expr (f : geom3d_frame_expr) : geom3d_space_expr f :=
  geom3d_space_expr.mk

instance has_one_displacement3d_expr : has_one (displacement3d_expr sp) := ⟨displacement3d_expr.one⟩
instance has_add_displacement3d_expr : has_add (displacement3d_expr sp) := ⟨λ v1 v2, displacement3d_expr.add_displacement3d_displacement3d v1 v2 ⟩
instance has_zero_displacement3d_expr : has_zero (displacement3d_expr sp) := ⟨displacement3d_expr.zero⟩

instance has_neg_displacement3d_expr : has_neg (displacement3d_expr sp) := ⟨λv1, displacement3d_expr.neg_displacement3d v1⟩
instance has_sub_displacement3d_expr : has_sub (displacement3d_expr sp) := ⟨λ v1 v2, displacement3d_expr.sub_displacement3d_displacement3d v1 v2⟩ 

instance : has_vadd (displacement3d_expr sp) (position3d_expr sp) := ⟨λv p, position3d_expr.add_displacement3d_position3d v p⟩
instance : has_vsub (displacement3d_expr sp) (position3d_expr sp) := ⟨λt1 t2, displacement3d_expr.sub_position3d_position3d t1 t2⟩


notation t+ᵥv := has_vadd.vadd v t
notation k•d :=  displacement3d_expr.smul_displacement3d k d
notation d•k :=  displacement3d_expr.smul_displacement3d k d
notation tr⬝d := displacement3d_expr.apply_displacement3dation_lit tr d
notation tr⬝t := position3d_expr.apply_position3d_lit tr t
notation tr∘tr := geom3d_transform_expr.compose_lit tr tr

class geom3d_transform_has_complit 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) 
  {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2)
  {f3 : geom3d_frame_expr} (sp3 : geom3d_space_expr f3)  
  := 
  (cast : 
    geom3d_transform sp1.value sp2.value → 
    geom3d_transform sp2.value sp3.value →
    geom3d_transform_expr sp1 sp3)
notation tr1`∘`tr2 := geom3d_transform_has_complit.cast tr1 tr2
noncomputable instance g3dcomplit
  {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} 
  {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2}
  {f3 : geom3d_frame_expr} {sp3 : geom3d_space_expr f3} : geom3d_transform_has_complit sp1 sp2 sp3 := 
    ⟨λt1 t2, geom3d_transform_expr.compose_lit t1 t2⟩ 


class geom3d_transform_has_comp 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) 
  {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2)
  {f3 : geom3d_frame_expr} (sp3 : geom3d_space_expr f3)  
  := 
  (cast : 
    geom3d_transform_expr sp1 sp2 → 
    geom3d_transform_expr sp2 sp3 →
    geom3d_transform_expr sp1 sp3)
notation tr1`∘`tr2 := geom3d_transform_has_comp.cast tr1 tr2
instance g3dcomp
  {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} 
  {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2}
  {f3 : geom3d_frame_expr} {sp3 : geom3d_space_expr f3} : geom3d_transform_has_comp sp1 sp2 sp3 := 
    ⟨λt1 t2, geom3d_transform_expr.compose t1 t2⟩ 


structure orientation3d_var {f : geom3d_frame_expr} (sp : geom3d_space_expr f) extends var

inductive orientation3d_expr {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : Type 1
| lit (v : orientation3d sp.value) : orientation3d_expr

class orientation3d_has_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) := 
  (cast : orientation3d sp.value → orientation3d_expr sp)
notation `|`tlit`|` := orientation3d_has_lit.cast tlit

instance orientation3d_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : orientation3d_has_lit  sp := 
  ⟨λt : orientation3d sp.value, orientation3d_expr.lit t⟩


abbreviation orientation3d_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) :=
  orientation3d_var sp → orientation3d sp.value
abbreviation orientation3d_eval := Π{f : geom3d_frame_expr} (sp : geom3d_space_expr f),
  orientation3d_env sp → orientation3d_expr sp → orientation3d sp.value


noncomputable def default_orientation3d_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : orientation3d_env sp := 
  λv, mk_orientation3d sp.value 1 0 0 0 1 0 0 0 1
    --(mk_displacement3d sp.value 1 2 3) (mk_displacement3d sp.value 1 2 3) (mk_displacement3d sp.value 1 2 3) 
def default_orientation3d_eval : orientation3d_eval := λf s, λenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_
  end

def static_orientation3d_eval : orientation3d_eval 
| f sp env_ (orientation3d_expr.lit or) := or

noncomputable def orientation3d_expr.value {f : geom3d_frame_expr} {sp : geom3d_space_expr f} (expr_ : orientation3d_expr sp)  
    : orientation3d sp.value :=
  (static_orientation3d_eval sp) (default_orientation3d_env sp) expr_


structure rotation3d_var {f : geom3d_frame_expr} (sp : geom3d_space_expr f) extends var

inductive rotation3d_expr {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : Type 1
| lit (v : rotation3d sp.value) : rotation3d_expr

class rotation3d_has_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) := 
  (cast : rotation3d sp.value → rotation3d_expr sp)
notation `|`tlit`|` := rotation3d_has_lit.cast tlit

instance rotation3d_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : rotation3d_has_lit  sp := 
  ⟨λt : rotation3d sp.value, rotation3d_expr.lit t⟩


abbreviation rotation3d_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) :=
  rotation3d_var sp → rotation3d sp.value
abbreviation rotation3d_eval := Π{f : geom3d_frame_expr} (sp : geom3d_space_expr f),
  rotation3d_env sp → rotation3d_expr sp → rotation3d sp.value


noncomputable def default_rotation3d_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : rotation3d_env sp := 
  λv, mk_rotation3d sp.value 1 0 0 0 1 0 0 0 1
  --  (mk_displacement3d sp.value 1 2 3) (mk_displacement3d sp.value 1 2 3) (mk_displacement3d sp.value 1 2 3) 
def default_rotation3d_eval : rotation3d_eval := λf s, λenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_
  end
  
def static_rotation3d_eval : rotation3d_eval 
| f sp env_ (rotation3d_expr.lit or) := or

noncomputable def rotation3d_expr.value {f : geom3d_frame_expr} {sp : geom3d_space_expr f} (expr_ : rotation3d_expr sp)  
    : rotation3d sp.value :=
  (static_rotation3d_eval sp) (default_rotation3d_env sp) expr_



structure pose3d_var {f : geom3d_frame_expr} (sp : geom3d_space_expr f) extends var

inductive pose3d_expr {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : Type 1
| lit (v : pose3d sp.value) : pose3d_expr
| apply_pose3d_lit {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} (v : geom3d_transform_expr sp2 sp) 
    (t : pose3d sp2.value) : pose3d_expr

class pose3d_has_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) := 
  (cast : pose3d sp.value → pose3d_expr sp)
notation `|`tlit`|` := pose3d_has_lit.cast tlit

instance pose3d_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : pose3d_has_lit  sp := 
  ⟨λt : pose3d sp.value, pose3d_expr.lit t⟩


abbreviation pose3d_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) :=
  pose3d_var sp → pose3d sp.value
abbreviation pose3d_eval := Π{f : geom3d_frame_expr} (sp : geom3d_space_expr f),
  pose3d_env sp → pose3d_expr sp → pose3d sp.value


noncomputable def default_pose3d_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : pose3d_env sp := 
  λv, mk_pose3d sp.value 
    (mk_orientation3d sp.value 1 0 0 0 1 0 0 0 1)
    --(mk_displacement3d sp.value 0 0 0) (mk_displacement3d sp.value 0 0 0) (mk_displacement3d sp.value 0 0 0)) 
    (mk_position3d sp.value 0 0 0)
    
noncomputable def default_pose3d_eval : pose3d_eval := λf s, λenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact mk_pose3d s.value
    (mk_orientation3d _ 1 0 0 0 1 0 0 0 1)
    (mk_position3d _ 0 0 0)
  end
  
noncomputable def static_pose3d_eval : pose3d_eval 
| f sp env_ (pose3d_expr.lit or) := or
| f sp env_ (pose3d_expr.apply_pose3d_lit tr p) := 
  (tr.value.transform_pose3d p)

noncomputable def pose3d_expr.value {f : geom3d_frame_expr} {sp : geom3d_space_expr f} (expr_ : pose3d_expr sp)  
    : pose3d sp.value :=
  (static_pose3d_eval sp) (default_pose3d_env sp) expr_

open lang.time

structure pose3d_time_series_var {f : geom3d_frame_expr} (sp : geom3d_space_expr f) extends var

inductive pose3d_time_series_expr {tf : time_frame_expr} (ts : time_space_expr tf) {f : geom3d_frame_expr} (sp : geom3d_space_expr f): Type 1
| lit (v : pose3d_discrete ts.value sp.value) : pose3d_time_series_expr
| apply_pose3d_lit {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} (v : geom3d_transform_expr sp2 sp) 
    (t : pose3d sp2.value) : pose3d_time_series_expr

class pose3d_time_series_has_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) {tf : time_frame_expr} (ts : time_space_expr tf) := 
  (cast : pose3d_discrete ts.value sp.value → pose3d_time_series_expr ts sp)
notation `|`tlit`|` := pose3d_has_lit.cast tlit

instance pose3d_time_series_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : pose3d_has_lit  sp := 
  ⟨λt : pose3d sp.value, pose3d_expr.lit t⟩


abbreviation pose3d_time_series_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) :=
  pose3d_var sp → pose3d sp.value
abbreviation pose3d_time_series_eval := Π{f : geom3d_frame_expr} (sp : geom3d_space_expr f),
  pose3d_env sp → pose3d_expr sp → pose3d sp.value


noncomputable def default_pose3d_time_series_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : pose3d_env sp := 
  λv, mk_pose3d sp.value 
    (mk_orientation3d sp.value 1 0 0 0 1 0 0 0 1)
    --(mk_displacement3d sp.value 0 0 0) (mk_displacement3d sp.value 0 0 0) (mk_displacement3d sp.value 0 0 0)) 
    (mk_position3d sp.value 0 0 0)
    
noncomputable def default_pose3d_time_series_eval : pose3d_eval := λf s, λenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact mk_pose3d s.value
    (mk_orientation3d _ 1 0 0 0 1 0 0 0 1)
    (mk_position3d _ 0 0 0)
  end
  
noncomputable def static_pose3d_time_series_eval : pose3d_eval 
| f sp env_ (pose3d_expr.lit or) := or
| f sp env_ (pose3d_expr.apply_pose3d_lit tr p) := 
  (tr.value.transform_pose3d p)

noncomputable def pose3d_time_series_expr.value {f : geom3d_frame_expr} {sp : geom3d_space_expr f} (expr_ : pose3d_expr sp)  
    : pose3d sp.value :=
  (static_pose3d_eval sp) (default_pose3d_env sp) expr_
end lang.geom3d
