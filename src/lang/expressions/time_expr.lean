import .expr_base
import ...phys.time.time
import .scalar_expr

namespace lang.time

universes u

structure time_frame_var extends var 


inductive time_frame_expr : Type 1 --{f : fm scalar T}
| lit (f : time_frame) : time_frame_expr
| var (v : time_frame_var) : time_frame_expr


abbreviation time_frame_env :=
  time_frame_var → time_frame
abbreviation time_frame_eval :=
  time_frame_env → time_frame_expr → time_frame

noncomputable def default_frame_env : time_frame_env := 
  λv, time_std_frame
noncomputable def default_frame_eval : time_frame_eval := λenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact (default_frame_env expr_)
  end

def static_frame_eval : time_frame_eval 
| env_ (time_frame_expr.lit f) := f
| env_ (time_frame_expr.var v) := env_ v

noncomputable def time_frame_expr.value (expr_ : time_frame_expr) : time_frame :=
  (static_frame_eval) (default_frame_env) expr_

structure time_space_var (f : time_frame_expr) extends var

inductive time_space_expr (f : time_frame_expr) : Type 1
| lit (sp : time_space f.value) : time_space_expr
| var (v : time_space_var f) : time_space_expr
| mk : time_space_expr

abbreviation time_space_env := Π(f : time_frame_expr),
  time_space_var f → time_space f.value
abbreviation time_space_eval := Π(f : time_frame_expr),
  time_space_env → time_space_expr f → time_space f.value


noncomputable def default_space_env : time_space_env := 
  λf, λv, mk_space f.value
noncomputable def default_space_eval : time_space_eval := λf, λenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact (default_space_env f expr_),
    exact mk_space f.value
  end

noncomputable def static_space_eval : time_space_eval 
| f env_ (time_space_expr.lit sp) := sp
| f env_ (time_space_expr.var v) := env_ f v
| f env_ (time_space_expr.mk) := mk_space f.value

noncomputable def time_space_expr.value {f : time_frame_expr} (expr_ : time_space_expr f)  : time_space f.value :=
  (static_space_eval f) (default_space_env) expr_

structure transform_var  
  {f1 : time_frame_expr} (sp1 : time_space_expr f1) {f2 : time_frame_expr} (sp2 : time_space_expr f2) extends var

inductive time_transform_expr
  : Π {f1 : time_frame_expr} (sp1 : time_space_expr f1), Π {f2 : time_frame_expr} (sp2 : time_space_expr f2), Type 1
| lit {f1 : time_frame_expr} {sp1 : time_space_expr f1} {f2 : time_frame_expr} {sp2 : time_space_expr f2} (p : time_transform sp1.value sp2.value) : time_transform_expr sp1 sp2
| var {f1 : time_frame_expr} {sp1 : time_space_expr f1} {f2 : time_frame_expr} {sp2 : time_space_expr f2} (v : transform_var sp1 sp2) : time_transform_expr sp1 sp2
| compose_lit {f1 : time_frame_expr} {sp1 : time_space_expr f1} {f2 : time_frame} {sp2 : time_space f2} (t1 : time_transform sp1.value sp2) 
  {f3 : time_frame_expr} {sp3 : time_space_expr f3}  (t2 : time_transform sp2 sp3.value) : time_transform_expr sp1 sp3
| inv_lit {f1 : time_frame_expr} {sp1 : time_space_expr f1} {f2 : time_frame_expr} {sp2 : time_space_expr f2} (t : time_transform sp2.value sp1.value) : time_transform_expr sp1 sp2
| compose 
  {f1 : time_frame_expr} {sp1 : time_space_expr f1}
  {f2 : time_frame_expr} {sp2 : time_space_expr f2}
  {f3 : time_frame_expr} {sp3 : time_space_expr f3}
  (t1 : time_transform_expr sp1 sp3) (t2 : time_transform_expr sp3 sp2) : time_transform_expr sp1 sp2
| inv
  {f1 : time_frame_expr} {sp1 : time_space_expr f1}
  {f2 : time_frame_expr} {sp2 : time_space_expr f2}
  (tr : time_transform_expr sp2 sp1) : time_transform_expr sp1 sp2

class time_transform_has_lit 
  {f1 : time_frame_expr} (sp1 : time_space_expr f1) {f2 : time_frame_expr} (sp2 : time_space_expr f2) := 
  (cast : time_transform sp1.value sp2.value → time_transform_expr sp1 sp2)
notation `|`tlit`|` := time_transform_has_lit.cast tlit

instance time_transform_lit 
  {f1 : time_frame_expr} {sp1 : time_space_expr f1} {f2 : time_frame_expr} {sp2 : time_space_expr f2} : time_transform_has_lit sp1 sp2 := 
  ⟨λt, time_transform_expr.lit t⟩

abbreviation transform_env 
  {f1 : time_frame_expr} (sp1 : time_space_expr f1) {f2 : time_frame_expr} (sp2 : time_space_expr f2)  := 
  transform_var sp1 sp2 → time_transform sp1.value sp2.value

abbreviation transform_eval 
  {f1 : time_frame_expr} (sp1 : time_space_expr f1) {f2 : time_frame_expr} (sp2 : time_space_expr f2) := 
  transform_env sp1 sp2 → time_transform_expr sp1 sp2 → time_transform sp1.value sp2.value


noncomputable def default_transform_env 
  {f1 : time_frame_expr} (sp1 : time_space_expr f1) {f2 : time_frame_expr} (sp2 : time_space_expr f2) : transform_env sp1 sp2:=
    λv, sp1.value.mk_time_transform_to sp2.value

noncomputable def default_transform_eval 
  {f1 : time_frame_expr} (sp1 : time_space_expr f1) {f2 : time_frame_expr} (sp2 : time_space_expr f2) : transform_eval sp1 sp2 :=
  λenv_, λexpr_,  sp1.value.mk_time_transform_to sp2.value

noncomputable def static_transform_eval 
  {f1 : time_frame_expr} (sp1 : time_space_expr f1) {f2 : time_frame_expr} (sp2 : time_space_expr f2) : transform_eval sp1 sp2 
| env_ (time_transform_expr.lit tr) := tr
| env_ (time_transform_expr.var v) := env_ v
| env_ (time_transform_expr.compose_lit t1 t2) := ⟨⟨t1.1.1.trans t2.1.1⟩⟩
| env_ (time_transform_expr.inv_lit t) := ⟨⟨(t.1.1).symm⟩⟩
| env_ expr_ := default_transform_eval sp1 sp2 (default_transform_env sp1 sp2) expr_

noncomputable def time_transform_expr.value {f1 : time_frame_expr} {sp1 : time_space_expr f1} {f2 : time_frame_expr} {sp2 : time_space_expr f2}
  (expr_ : time_transform_expr sp1 sp2) : time_transform sp1.value sp2.value :=
  ((static_transform_eval sp1 sp2) (default_transform_env sp1 sp2) expr_)

class transform_has_inv 
  {f1 : time_frame_expr} (sp1 : time_space_expr f1) {f2 : time_frame_expr} (sp2 : time_space_expr f2) := 
  (inv : time_transform_expr sp1 sp2 → time_transform_expr sp2 sp1)
notation tr⁻¹:= transform_has_inv.inv tr

noncomputable instance transform_inv {f1 : time_frame_expr} {sp1 : time_space_expr f1} {f2 : time_frame_expr} {sp2 : time_space_expr f2} 
  : transform_has_inv sp1 sp2 := ⟨λt,
    begin
      let lit := t.value,
     exact (time_transform_expr.inv_lit lit),
    end⟩

noncomputable def time_transform_expr.trans 
  {f1 : time_frame_expr} {sp1 : time_space_expr f1} {f2 : time_frame_expr} {sp2 : time_space_expr f2}
 {f3 : time_frame_expr} {sp3 : time_space_expr f3} (expr_ : time_transform_expr sp1 sp2) : time_transform_expr sp2 sp3 → time_transform_expr sp1 sp3 
 := λt2,
 time_transform_expr.compose_lit expr_.value t2.value

structure duration_var {f : time_frame_expr} (sp : time_space_expr f) extends var 

structure time_var  {f : time_frame_expr} (sp : time_space_expr f) extends var
set_option trace.app_builder true --need to fix scalar for this to work

mutual inductive duration_expr, time_expr {f : time_frame_expr} (sp : time_space_expr f)
with duration_expr : Type 1
| zero : duration_expr
| one : duration_expr 
| lit (v : duration sp.value) : duration_expr
| var (v : duration_var sp) : duration_expr
| add_dur_dur (d1 : duration_expr) (d2 : duration_expr) : duration_expr
| neg_dur (d : duration_expr) : duration_expr
| sub_dur_dur (d1 : duration_expr) (d2 : duration_expr) : duration_expr
| sub_time_time (t1 : time_expr) (t2 : time_expr) : duration_expr
| smul_dur (k : scalar_expr) (d : duration_expr) : duration_expr
| apply_duration_lit {f2 : time_frame_expr} {sp2 : time_space_expr f2} (v : time_transform_expr sp2 sp) 
    (d : duration sp2.value) : duration_expr
with time_expr : Type 1
| lit (p : time sp.value) : time_expr
| var (v : time_var sp) : time_expr
| add_dur_time (d : duration_expr) (t : time_expr) : time_expr
| apply_time_lit {f2 : time_frame_expr} {sp2 : time_space_expr f2} (v : time_transform_expr sp2 sp) 
    (t : time sp2.value) : time_expr


abbreviation duration_env {f : time_frame_expr} (sp : time_space_expr f) := 
  duration_var sp → duration sp.value

attribute [elab_as_eliminator] 
abbreviation time_env {f : time_frame_expr} (sp : time_space_expr f) :=
  time_var sp → time sp.value

abbreviation duration_eval := Π{f : time_frame_expr} (sp : time_space_expr f),
  time_env sp → duration_env sp → duration_expr sp → duration sp.value

abbreviation time_eval := Π{f : time_frame_expr} (sp : time_space_expr f), 
  time_env sp → duration_env sp → time_expr sp → time sp.value

@[simp]
noncomputable def default_duration_env {f : time_frame_expr} (sp : time_space_expr f) : duration_env sp := λv, (mk_duration sp.value 1)

@[simp]
noncomputable def default_duration_eval : duration_eval  
  := λf sp, λtenv_, λdenv_, λexpr_, 
  begin
    repeat {exact (mk_duration sp.value 1)}
  end

@[simp]
noncomputable def default_time_env {f : time_frame_expr} (sp : time_space_expr f) : time_env sp 
  := (λv, (mk_time sp.value 1))


set_option eqn_compiler.max_steps 8192
@[simp, reducible]
noncomputable mutual def static_duration_eval, static_time_eval 
with static_duration_eval : duration_eval 
| f sp tenv_ denv_ (duration_expr.zero) := 0
| f sp tenv_ denv_ (duration_expr.one) := mk_duration sp.value 1
| f sp tenv_ denv_ (duration_expr.lit d) := d
| f sp tenv_ denv_ (duration_expr.var v) := denv_ v
| f sp tenv_ denv_ (duration_expr.add_dur_dur d1 d2) := (static_duration_eval sp tenv_ denv_ d1) +ᵥ (static_duration_eval sp tenv_ denv_ d2)
| f sp tenv_ denv_ (duration_expr.neg_dur d) := -(static_duration_eval sp tenv_ denv_ d)
| f sp tenv_ denv_ (duration_expr.sub_dur_dur d1 d2) := (static_duration_eval sp tenv_ denv_ d1) -ᵥ (static_duration_eval sp tenv_ denv_ d2)
| f sp tenv_ denv_ (duration_expr.sub_time_time t1 t2) := (static_time_eval sp tenv_ denv_ t1) -ᵥ (static_time_eval sp tenv_ denv_ t2)
| f sp tenv_ denv_ (duration_expr.smul_dur s d) := (static_scalar_eval default_scalar_env s)•(static_duration_eval sp tenv_ denv_ d)
| f sp tenv_ denv_ (duration_expr.apply_duration_lit t d) := t.value.transform_duration d
with static_time_eval : time_eval
| f sp tenv_ denv_ (time_expr.lit p) := p
| f sp tenv_ denv_ (time_expr.var v) := tenv_ v
| f sp tenv_ denv_ (time_expr.add_dur_time d t) := (static_duration_eval sp tenv_ denv_ d) +ᵥ (static_time_eval sp tenv_ denv_ t)
| f sp tenv_ denv_ (time_expr.apply_time_lit tr t) := tr.value.transform_time t

@[simp]
noncomputable def default_time_eval : time_eval := λf sp, λtenv_, λdenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact default_time_env sp expr_,
    repeat {exact (mk_time sp.value 1)}
  end

@[simp]
noncomputable def time_expr.value {f : time_frame_expr} {sp : time_space_expr f} (expr_ : time_expr sp) : time sp.value :=
  (static_time_eval sp) (default_time_env sp) (default_duration_env sp) expr_

@[simp]
noncomputable def duration_expr.value {f : time_frame_expr} {sp : time_space_expr f} (expr_ : duration_expr sp) : duration sp.value :=
  (static_duration_eval sp) (default_time_env sp) (default_duration_env sp) expr_

class time_has_lit {f : time_frame_expr} (sp : time_space_expr f) := 
  (cast : time sp.value → time_expr sp)
notation `|`tlit`|` := time_has_lit.cast tlit

instance time_lit {f : time_frame_expr} (sp : time_space_expr f) : time_has_lit  sp := 
  ⟨λt : time sp.value, time_expr.lit t⟩

class duration_has_lit {f : time_frame_expr} (sp : time_space_expr f) := 
  (cast : duration sp.value → duration_expr sp)
notation `|`tlit`|` := duration_has_lit.cast tlit

instance duration_lit {f : time_frame_expr} (sp : time_space_expr f) : duration_has_lit  sp := 
  ⟨λt : duration sp.value, duration_expr.lit t⟩

class time_frame_has_lit := 
  (cast : time_frame → time_frame_expr)
notation `|`flit`|` := time_frame_has_lit.cast flit

instance time_frame_lit : time_frame_has_lit := 
  ⟨λf, time_frame_expr.lit f⟩

class time_space_has_lit (f : time_frame_expr ) := 
  (cast : time_space f.value  → time_space_expr f)
notation `|`slit`|` := time_space_has_lit.cast slit

instance time_space_lit {f : time_frame_expr} : time_space_has_lit f := 
  ⟨λs, time_space_expr.lit s⟩


variables  {f : time_frame_expr} {sp : time_space_expr f} 

#check mk_frame
noncomputable def mk_time_frame_expr {f : time_frame_expr} {sp : time_space_expr f} (o : time_expr sp) (b : duration_expr sp) : time_frame_expr :=
  |(mk_time_frame o.value b.value)|

def mk_time_space_expr (f : time_frame_expr) : time_space_expr f :=
  time_space_expr.mk


instance has_one_dur_expr : has_one (duration_expr sp) := ⟨duration_expr.one⟩
instance has_add_dur_expr : has_add (duration_expr sp) := ⟨λ v1 v2, duration_expr.add_dur_dur v1 v2 ⟩
instance has_zero_dur_expr : has_zero (duration_expr sp) := ⟨duration_expr.zero⟩

instance has_neg_dur_expr : has_neg (duration_expr sp) := ⟨λv1, duration_expr.neg_dur v1⟩
instance has_sub_dur_expr : has_sub (duration_expr sp) := ⟨λ v1 v2, duration_expr.sub_dur_dur v1 v2⟩ 

instance : has_vadd (duration_expr sp) (time_expr sp) := ⟨λv p, time_expr.add_dur_time v p⟩
instance : has_vsub (duration_expr sp) (time_expr sp) := ⟨λt1 t2, duration_expr.sub_time_time t1 t2⟩


notation t+ᵥv := has_vadd.vadd v t
notation k•d :=  duration_expr.smul_dur k d
notation d•k :=  duration_expr.smul_dur k d
notation tr⬝d := duration_expr.apply_duration_lit tr d
notation tr⬝t := time_expr.apply_time_lit tr t
notation tr∘tr := time_transform_expr.compose_lit tr tr

class time_transform_has_complit 
  {f1 : time_frame_expr} (sp1 : time_space_expr f1) 
  {f2 : time_frame_expr} (sp2 : time_space_expr f2)
  {f3 : time_frame_expr} (sp3 : time_space_expr f3)  
  := 
  (cast : 
    time_transform sp1.value sp2.value → 
    time_transform sp2.value sp3.value →
    time_transform_expr sp1 sp3)
notation tr1`∘`tr2 := time_transform_has_complit.cast tr1 tr2
noncomputable instance timetrcomplit
  {f1 : time_frame_expr} {sp1 : time_space_expr f1} 
  {f2 : time_frame_expr} {sp2 : time_space_expr f2}
  {f3 : time_frame_expr} {sp3 : time_space_expr f3} : time_transform_has_complit sp1 sp2 sp3 := 
    ⟨λt1 t2, time_transform_expr.compose_lit t1 t2⟩ 


class time_transform_has_comp 
  {f1 : time_frame_expr} (sp1 : time_space_expr f1) 
  {f2 : time_frame_expr} (sp2 : time_space_expr f2)
  {f3 : time_frame_expr} (sp3 : time_space_expr f3)  
  := 
  (cast : 
    time_transform_expr sp1 sp2 → 
    time_transform_expr sp2 sp3 →
    time_transform_expr sp1 sp3)
notation tr1`∘`tr2 := time_transform_has_comp.cast tr1 tr2
instance timetrcomp
  {f1 : time_frame_expr} {sp1 : time_space_expr f1} 
  {f2 : time_frame_expr} {sp2 : time_space_expr f2}
  {f3 : time_frame_expr} {sp3 : time_space_expr f3} : time_transform_has_comp sp1 sp2 sp3 := 
    ⟨λt1 t2, time_transform_expr.compose t1 t2⟩ 


end lang.time
