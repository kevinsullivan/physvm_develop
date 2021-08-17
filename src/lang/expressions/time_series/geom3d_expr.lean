--import ....phys.geom.geom3d
import ..geom3d_expr
--import .....phys.series.geom3d
import ..time_expr
import ......phys.geom.geom3d
import ......phys.time_series.geom3d


namespace lang.series.geom3d

universes u

open lang.geom3d
open lang.time

variables {fr : time_frame_expr} (ts : time_space_expr fr)


structure timestamped_geom3d_transform_var 
  {fr : time_frame_expr} (ts : time_space_expr fr) {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} 
    (sp2 : geom3d_space_expr f2)  extends var

inductive timestamped_geom3d_transform_expr 
  : Π {fr : time_frame_expr} (ts : time_space_expr fr), 
    Π {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1), Π {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2), Type 1
| lit {fr : time_frame_expr} {ts : time_space_expr fr} {f1 : geom3d_frame_expr} 
    {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2}
  (l : timestamped ts.value (geom3d_transform sp1.value sp2.value)): timestamped_geom3d_transform_expr ts sp1 sp2
| lit_time {fr : time_frame_expr} {ts : time_space_expr fr} {f1 : geom3d_frame_expr} 
    {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2}
  (te : time_expr ts) (pe : geom3d_transform_expr sp1 sp2): timestamped_geom3d_transform_expr ts sp1 sp2

class timestamped_geom3d_transform_has_lit 
  {fr : time_frame_expr} (ts : time_space_expr fr)
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) := 
  (cast : timestamped ts.value (geom3d_transform sp1.value sp2.value) → timestamped_geom3d_transform_expr ts sp1 sp2)

notation `|`tlit`|` := timestamped_geom3d_transform_has_lit.cast tlit

instance timestamped_geom3d_transform_lit 
  {fr : time_frame_expr} (ts : time_space_expr fr) 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2)
  : timestamped_geom3d_transform_has_lit ts sp1 sp2 := 
  ⟨λt, timestamped_geom3d_transform_expr.lit t⟩


abbreviation timestamped_geom3d_transform_env 
  {fr : time_frame_expr} (ts : time_space_expr fr) {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} 
    (sp2 : geom3d_space_expr f2) :=
  timestamped_geom3d_transform_var ts sp1 sp2 → 
    timestamped ts.value (geom3d_transform sp1.value sp2.value)
abbreviation timestamped_geom3d_transform_eval := 
  Π{fr : time_frame_expr} (ts : time_space_expr fr),
  Π{f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1)
   {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) ,
  timestamped_geom3d_transform_env ts sp1 sp2 → timestamped_geom3d_transform_expr ts sp1 sp2 → 
    timestamped ts.value (geom3d_transform sp1.value sp2.value)


@[simp]
noncomputable def default_timestamped_geom3d_transform_env 
    {fr : time_frame_expr} (ts : time_space_expr fr) {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} 
    (sp2 : geom3d_space_expr f2) : timestamped_geom3d_transform_env ts sp1 sp2 := 
  λv, @mk_default_timestamped fr.value ts.value (geom3d_transform sp1.value sp2.value) _
    
--set_option eqn_compiler.max_steps 16384
@[simp]
noncomputable def default_timestamped_geom3d_transform_eval : timestamped_geom3d_transform_eval
:= λtf ts gf gs gf2 gs2, λenv_, λexpr_, 
   @mk_default_timestamped tf.value ts.value (geom3d_transform gs.value gs2.value) _

@[simp]
noncomputable def static_timestamped_geom3d_transform_eval : timestamped_geom3d_transform_eval
| tf ts gf gs gf2 gs2 env_ (timestamped_geom3d_transform_expr.lit p) := p
| tf ts gf gs gf2 gs2 env_ (timestamped_geom3d_transform_expr.lit_time te pe) := ⟨te.value, pe.value⟩

@[simp]
noncomputable def timestamped_geom3d_transform_expr.value
    {fr : time_frame_expr} {ts : time_space_expr fr} {f1 : geom3d_frame_expr} 
    {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} 
    (expr_ : timestamped_geom3d_transform_expr ts sp1 sp2)  
    : timestamped ts.value (geom3d_transform sp1.value sp2.value) :=
  (static_timestamped_geom3d_transform_eval ts sp1 sp2) (default_timestamped_geom3d_transform_env ts sp1 sp2) expr_


structure geom3d_transform_series_var  
  {fr : time_frame_expr} (ts : time_space_expr fr) {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} 
    (sp2 : geom3d_space_expr f2) extends var

  #check geom3d_transform_discrete

inductive geom3d_transform_series_expr
  : Π {fr : time_frame_expr} (ts : time_space_expr fr), 
    Π {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1), Π {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2), Type 1
| lit {fr : time_frame_expr} {ts : time_space_expr fr} {f1 : geom3d_frame_expr} 
    {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} 
    (p : geom3d_transform_discrete ts.value sp1.value sp2.value) : geom3d_transform_series_expr ts sp1 sp2
| var {fr : time_frame_expr} {ts : time_space_expr fr}  {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} 
    (v : geom3d_transform_series_var ts sp1 sp2) : geom3d_transform_series_expr ts sp1 sp2
| update {fr : time_frame_expr} {ts : time_space_expr fr} {f1 : geom3d_frame_expr} 
    {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} 
    (ges : geom3d_transform_series_expr ts sp1 sp2) 
    (te : time_expr ts) (ge : geom3d_transform_expr sp1 sp2) 
    : geom3d_transform_series_expr ts sp1 sp2
| update_ts {fr : time_frame_expr} {ts : time_space_expr fr} {f1 : geom3d_frame_expr} 
    {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} 
    (ges : geom3d_transform_series_expr ts sp1 sp2) 
    (te : timestamped_geom3d_transform_expr ts sp1 sp2) 
    : geom3d_transform_series_expr ts sp1 sp2

class geom3d_transform_series_has_lit 
  {fr : time_frame_expr} (ts : time_space_expr fr)
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) := 
  (cast : geom3d_transform_discrete ts.value sp1.value sp2.value → geom3d_transform_series_expr ts sp1 sp2)

notation `|`tlit`|` := geom3d_transform_series_has_lit.cast tlit

instance geom3d_transform_series_lit 
  {fr : time_frame_expr} (ts : time_space_expr fr) 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2)
  : geom3d_transform_series_has_lit ts sp1 sp2 := 
  ⟨λt, geom3d_transform_series_expr.lit t⟩

class  timestamped_geom3d_transform_expr_has_maplit {tf : time_frame_expr} (ts : time_space_expr tf)
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2):= 
  (cast : time_expr ts → geom3d_transform_expr sp1 sp2 → timestamped_geom3d_transform_expr ts sp1 sp2)
notation T`↦`E := timestamped_geom3d_transform_expr_has_maplit.cast T E
notation |T,E| := timestamped_geom3d_transform_expr_has_maplit.case T E

instance timestamped_geom3d_transform_expr_map_lit {tf : time_frame_expr} (ts : time_space_expr tf)
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2)
  : timestamped_geom3d_transform_expr_has_maplit ts sp1 sp2 := 
  ⟨λte pe , timestamped_geom3d_transform_expr.lit_time te pe⟩


class geom3d_transform_series_has_updatets{tf : time_frame_expr} (ts : time_space_expr tf)
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) := 
  (cast : geom3d_transform_series_expr ts sp1 sp2 → timestamped_geom3d_transform_expr ts sp1 sp2 → geom3d_transform_series_expr ts sp1 sp2)
notation S`[`GES`]` := geom3d_transform_series_has_updatets.cast S GES

instance geom3d_transform_series_update {tf : time_frame_expr} (ts : time_space_expr tf)
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) 
  : geom3d_transform_series_has_updatets ts  sp1 sp2 := 
  ⟨λpes ges, geom3d_transform_series_expr.update_ts pes ges⟩




abbreviation geom3d_transform_series_env 
  {fr : time_frame_expr} (ts : time_space_expr fr)
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2)  := 
  geom3d_transform_series_var ts sp1 sp2 → geom3d_transform_discrete ts.value sp1.value sp2.value

abbreviation geom3d_transform_series_eval :=
  Π{fr : time_frame_expr} (ts : time_space_expr fr),
  Π{f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1)
   {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) ,
  geom3d_transform_series_env ts sp1 sp2 → geom3d_transform_series_expr ts sp1 sp2 → geom3d_transform_discrete ts.value sp1.value sp2.value


@[simp]
noncomputable def default_geom3d_transform_series_env 
  {fr : time_frame_expr} (ts : time_space_expr fr)
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) 
    : geom3d_transform_series_env ts sp1 sp2:=
    λv, @mk_geom3d_transform_discrete_empty fr.value ts.value f1.value sp1.value f2.value sp2.value-- (sp1.value).mk_geom3d_transform_to sp2.value

@[simp]
noncomputable def default_geom3d_transform_series_eval 
  : geom3d_transform_series_eval :=
  λtf ts gf gs gf2 gs2, λenv_, λexpr_,  @mk_geom3d_transform_discrete_empty _ ts.value _ gs.value _ gs2.value

@[simp,reducible]
noncomputable def static_geom3d_transform_series_eval 
 -- {fr : time_frame_expr} (ts : time_space_expr fr)
 -- {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) {f2 : geom3d_frame_expr} (sp2 : geom3d_space_expr f2) 
  : geom3d_transform_series_eval --ts sp1 sp2 
| tf ts gf gs gf2 gs2 env_ (geom3d_transform_series_expr.lit tr) := tr
| tf ts gf gs gf2 gs2 env_ (geom3d_transform_series_expr.var v) := env_ v
| tf ts gf gs gf2 gs2 env_ (geom3d_transform_series_expr.update ges te ge) :=
  ((static_geom3d_transform_series_eval ts gs gs2) (default_geom3d_transform_series_env ts gs gs2) ges)
  .update ⟨te.value, ge.value⟩
| tf ts gf gs gf2 gs2 env_ (geom3d_transform_series_expr.update_ts ges tse) :=
  ((static_geom3d_transform_series_eval ts gs gs2) (default_geom3d_transform_series_env ts gs gs2) ges)
  .update tse.value



@[simp]
noncomputable def geom3d_transform_series_expr.value 
  {fr : time_frame_expr} {ts : time_space_expr fr}
  {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2}
  (expr_ : geom3d_transform_series_expr ts sp1 sp2) --: geom3d_transform_discrete ts.value sp1.value sp2.value 
  :=
  ((static_geom3d_transform_series_eval ts sp1 sp2) (default_geom3d_transform_series_env ts sp1 sp2) expr_)

variables 
          {f1 : geom3d_frame_expr} {sp1 : geom3d_space_expr f1} {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2}
          (expr_ : geom3d_transform_series_expr ts sp1 sp2)

structure displacement3d_var {f : geom3d_frame_expr} (sp : geom3d_space_expr f) extends var 

structure position3d_var  {f : geom3d_frame_expr} (sp : geom3d_space_expr f) extends var

mutual inductive displacement3d_series_expr, position3d_series_expr 
  {fr : time_frame_expr} (ts : time_space_expr fr)
  {f : geom3d_frame_expr} (sp : geom3d_space_expr f)
with displacement3d_series_expr : Type 1
| lit (v : displacement3d_discrete ts.value sp.value) : displacement3d_series_expr
| var (v : displacement3d_var sp) : displacement3d_series_expr
| update (se : displacement3d_series_expr) (te : time_expr ts) (de : displacement3d_expr sp) : displacement3d_series_expr
with position3d_series_expr : Type 1
| lit (p : position3d_discrete ts.value sp.value) : position3d_series_expr
| var (v : position3d_var sp) : position3d_series_expr
| update (se : position3d_series_expr) (te : time_expr ts) (de : position3d_expr sp) : position3d_series_expr
/-
abbreviation displacement3d_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) := 
  displacement3d_var sp → displacement3d_discrete sp.value

attribute [elab_as_eliminator] 
abbreviation position3d_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) :=
  position3d_var sp → position3d_discrete sp.value

abbreviation displacement3d_eval := Π{f : geom3d_frame_expr} (sp : geom3d_space_expr f),
  position3d_env sp → displacement3d_env sp → displacement3d_series_expr sp → displacement3d_discrete sp.value

abbreviation position3d_eval := Π{f : geom3d_frame_expr} (sp : geom3d_space_expr f), 
  position3d_env sp → displacement3d_env sp → position3d_series_expr sp → position3d_discrete sp.value

noncomputable def default_displacement3d_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : displacement3d_env sp := λv, (mk_displacement3d_discrete sp.value 1 1 1)
noncomputable def default_displacement3d_eval : displacement3d_eval  
  := λf sp, λtenv_, λdenv_, λexpr_, 
  begin
    repeat {exact (mk_displacement3d_discrete sp.value 1 1 1)}
  end

noncomputable def default_position3d_env {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : position3d_env sp 
  := (λv, (mk_position3d_discrete sp.value  1 1 1))


set_option eqn_compiler.max_steps 8192
noncomputable mutual def static_displacement3d_eval, static_position3d_eval 
with static_displacement3d_eval : displacement3d_eval 
| f sp tenv_ denv_ (displacement3d_series_expr.zero) := 0
| f sp tenv_ denv_ (displacement3d_series_expr.one) := mk_displacement3d_discrete sp.value 1 1 1
| f sp tenv_ denv_ (displacement3d_series_expr.lit d) := d
| f sp tenv_ denv_ (displacement3d_series_expr.var v) := denv_ v
| f sp tenv_ denv_ (displacement3d_series_expr.add_displacement3d_displacement3d_discrete d1 d2) := (static_displacement3d_eval sp tenv_ denv_ d1) +ᵥ (static_displacement3d_eval sp tenv_ denv_ d2)
| f sp tenv_ denv_ (displacement3d_series_expr.neg_displacement3d_discrete d) := -(static_displacement3d_eval sp tenv_ denv_ d)
| f sp tenv_ denv_ (displacement3d_series_expr.sub_displacement3d_displacement3d_discrete d1 d2) := (static_displacement3d_eval sp tenv_ denv_ d1) -ᵥ (static_displacement3d_eval sp tenv_ denv_ d2)
| f sp tenv_ denv_ (displacement3d_series_expr.sub_position3d_position3d_discrete t1 t2) := (static_position3d_eval sp tenv_ denv_ t1) -ᵥ (static_position3d_eval sp tenv_ denv_ t2)
| f sp tenv_ denv_ (displacement3d_series_expr.smul_displacement3d_discrete s d) := (static_real_scalar_eval default_real_scalar_env s)•(static_displacement3d_eval sp tenv_ denv_ d)
| f sp tenv_ denv_ (displacement3d_series_expr.apply_displacement3d_lit t d) := t.value.transform_displacement3d_discrete d
with static_position3d_eval : position3d_eval
| f sp tenv_ denv_ (position3d_series_expr.lit p) := p
| f sp tenv_ denv_ (position3d_series_expr.var v) := tenv_ v
| f sp tenv_ denv_ (position3d_series_expr.add_displacement3d_position3d_discrete d t) := (static_displacement3d_eval sp tenv_ denv_ d) +ᵥ (static_position3d_eval sp tenv_ denv_ t)
| f sp tenv_ denv_ (position3d_series_expr.apply_position3d_lit tr t) := tr.value.transform_position3d_discrete t


noncomputable def default_position3d_eval : position3d_eval := λf sp, λtenv_, λdenv_, λexpr_, 
  begin
    cases expr_,
    exact expr_,
    exact default_position3d_env sp expr_,
    repeat {exact (mk_position3d_discrete sp.value 1 1 1)}
  end

noncomputable def position3d_series_expr.value {f : geom3d_frame_expr} {sp : geom3d_space_expr f} (expr_ : position3d_series_expr sp) : position3d_discrete sp.value :=
  (static_position3d_eval sp) (default_position3d_env sp) (default_displacement3d_env sp) expr_

noncomputable def displacement3d_series_expr.value {f : geom3d_frame_expr} {sp : geom3d_space_expr f} (expr_ : displacement3d_series_expr sp) : displacement3d_discrete sp.value :=
  (static_displacement3d_eval sp) (default_position3d_env sp) (default_displacement3d_env sp) expr_


class position3d_has_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) := 
  (cast : position3d_discrete sp.value → position3d_series_expr sp)
notation `|`tlit`|` := position3d_has_lit.cast tlit

instance position3d_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : position3d_has_lit  sp := 
  ⟨λt : position3d_discrete sp.value, position3d_series_expr.lit t⟩

class displacement3d_has_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) := 
  (cast : displacement3d_discrete sp.value → displacement3d_series_expr sp)
notation `|`tlit`|` := displacement3d_has_lit.cast tlit

instance displacement3d_lit {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : displacement3d_has_lit  sp := 
  ⟨λt : displacement3d_discrete sp.value, displacement3d_series_expr.lit t⟩

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
-/
structure timestamped_pose3d_var {tf : time_frame_expr} (ts : time_space_expr tf) {f : geom3d_frame_expr} (sp : geom3d_space_expr f) extends var

inductive timestamped_pose3d_expr : 
  Π {tf : time_frame_expr} (ts : time_space_expr tf), 
  Π {f : geom3d_frame_expr} (sp : geom3d_space_expr f), Type 1
| lit {tf : time_frame_expr} {ts : time_space_expr tf} {f : geom3d_frame_expr}{sp : geom3d_space_expr f} 
  (l : timestamped ts.value (pose3d sp.value)): timestamped_pose3d_expr ts sp
| lit_time {tf : time_frame_expr} {ts : time_space_expr tf} {f : geom3d_frame_expr}{sp : geom3d_space_expr f} 
  (te : time_expr ts) (pe : pose3d_expr sp): timestamped_pose3d_expr ts sp

class timestamped_pose3d_expr_has_lit 
  {fr : time_frame_expr} (ts : time_space_expr fr)
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1)  := 
  (cast : timestamped ts.value (pose3d sp1.value) → timestamped_pose3d_expr ts sp1)

notation `|`tlit`|` := timestamped_pose3d_expr_has_lit.cast tlit

instance timestamped_pose3d_expr_lit 
  {fr : time_frame_expr} (ts : time_space_expr fr) 
  {f1 : geom3d_frame_expr} (sp1 : geom3d_space_expr f1) 
  : timestamped_pose3d_expr_has_lit ts sp1 := 
  ⟨λt, timestamped_pose3d_expr.lit t⟩

abbreviation timestamped_pose3d_env {tf : time_frame_expr} (ts : time_space_expr tf) {f : geom3d_frame_expr} (sp : geom3d_space_expr f) :=
  timestamped_pose3d_var ts sp → 
    timestamped ts.value (pose3d sp.value)
abbreviation timestamped_pose3d_eval := 
            Π {tf : time_frame_expr} (ts : time_space_expr tf), 
            Π{f : geom3d_frame_expr} (sp : geom3d_space_expr f),
  timestamped_pose3d_env ts sp → timestamped_pose3d_expr ts sp → 
    timestamped ts.value (pose3d sp.value)


@[simp]
noncomputable def default_timestamped_pose3d_env 
    {tf : time_frame_expr} (ts : time_space_expr tf) 
    {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : timestamped_pose3d_env ts sp := 
  λv, @mk_default_timestamped tf.value ts.value (pose3d sp.value) _
    
--set_option eqn_compiler.max_steps 16384
@[simp]
noncomputable def default_timestamped_pose3d_eval : timestamped_pose3d_eval
:= λtf ts gf gs, λenv_, λexpr_, 
   @mk_default_timestamped tf.value ts.value (pose3d gs.value) _


@[simp]
noncomputable def static_timestamped_pose3d_eval : timestamped_pose3d_eval
| tf ts gf gs env_ (timestamped_pose3d_expr.lit p) := p
| tf ts gf gs env_ (timestamped_pose3d_expr.lit_time te pe) := ⟨te.value, pe.value⟩

@[simp]
noncomputable def timestamped_pose3d_expr.value
    {tf : time_frame_expr} {ts : time_space_expr tf} 
     {f : geom3d_frame_expr} {sp : geom3d_space_expr f} (expr_ : timestamped_pose3d_expr ts sp)  
    : timestamped ts.value (pose3d sp.value) :=
  (static_timestamped_pose3d_eval ts sp) (default_timestamped_pose3d_env ts sp) expr_



structure pose3d_series_var {tf : time_frame_expr} (ts : time_space_expr tf) {f : geom3d_frame_expr} (sp : geom3d_space_expr f) extends var

inductive pose3d_series_expr :
  Π {tf : time_frame_expr} (ts : time_space_expr tf), 
  Π {f : geom3d_frame_expr} (sp : geom3d_space_expr f), Type 1
| lit {tf : time_frame_expr} {ts : time_space_expr tf} {f : geom3d_frame_expr}{sp : geom3d_space_expr f}
  (v : pose3d_discrete ts.value sp.value) : pose3d_series_expr ts sp
| update 
  {tf : time_frame_expr} {ts : time_space_expr tf} {f : geom3d_frame_expr}{sp : geom3d_space_expr f}
  (pes : pose3d_series_expr ts sp) (te : time_expr ts) (pe : pose3d_expr sp) : pose3d_series_expr ts sp
| update_ts
  {tf : time_frame_expr} {ts : time_space_expr tf} {f : geom3d_frame_expr}{sp : geom3d_space_expr f}
  (pes : pose3d_series_expr ts sp) (tse : timestamped_pose3d_expr ts sp) : pose3d_series_expr ts sp
--| apply_timestamped_transform_to_lit
--  {tf : time_frame_expr} {ts : time_space_expr tf} 
--  {f1 : geom3d_frame_expr}{sp1 : geom3d_space_expr f1}
--  {f2 : geom3d_frame_expr}{sp2 : geom3d_space_expr f2}
--  (pes : pose3d_series_expr ts sp) (tse : timestamped_pose3d_expr ts sp) : pose3d_series_expr ts sp

--| apply_latest_pose3d_lit {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2}
--    (pe : pose3d_series_expr)
--    (v : geom3d_transform_series_expr ts sp2 sp) 
--    (t : pose3d_discrete ts.value sp2.value) : pose3d_series_expr
--| apply_pose3d_lit {f2 : geom3d_frame_expr} {sp2 : geom3d_space_expr f2} 
--    (pe : pose3d_series_expr)
 --   (v : geom3d_transform_series_expr ts sp2 sp) 
--    (t : pose3d_discrete ts.value sp2.value) : pose3d_series_expr 

class pose3d_series_has_lit{tf : time_frame_expr} (ts : time_space_expr tf)  {f : geom3d_frame_expr} (sp : geom3d_space_expr f):= 
  (cast : pose3d_discrete ts.value sp.value → pose3d_series_expr ts sp)
notation `|`tlit`|` := pose3d_series_has_lit.cast tlit

instance pose3d_series_lit {tf : time_frame_expr} (ts : time_space_expr tf) {f : geom3d_frame_expr} (sp : geom3d_space_expr f) 
  : pose3d_series_has_lit ts  sp := 
  ⟨λt : pose3d_discrete ts.value sp.value, pose3d_series_expr.lit t⟩


class pose3d_series_has_update{tf : time_frame_expr} (ts : time_space_expr tf)  {f : geom3d_frame_expr} (sp : geom3d_space_expr f):= 
  (cast : pose3d_series_expr ts sp → timestamped_pose3d_expr ts sp → pose3d_series_expr ts sp)
notation S`[`TE`]` := pose3d_series_has_update.cast S TE
--notation S`[`T↦E`]`:= pose3d_series_has_update.cast S ⟨T,E\> 

instance pose3d_series_update {tf : time_frame_expr} (ts : time_space_expr tf) {f : geom3d_frame_expr} (sp : geom3d_space_expr f) 
  : pose3d_series_has_update ts  sp := 
  ⟨λpes tes, pose3d_series_expr.update_ts pes tes⟩

class  timestamped_pose3d_expr_has_maplit {tf : time_frame_expr} (ts : time_space_expr tf)  {f : geom3d_frame_expr} (sp : geom3d_space_expr f):= 
  (cast : time_expr ts → pose3d_expr sp → timestamped_pose3d_expr ts sp)
notation T`↦`E := timestamped_pose3d_expr_has_maplit.cast T E
notation `|`T`,`E`|` := timestamped_pose3d_expr_has_maplit.cast T E

instance timestamped_pose3d_expr_map_lit {tf : time_frame_expr} (ts : time_space_expr tf) {f : geom3d_frame_expr} (sp : geom3d_space_expr f) 
  : timestamped_pose3d_expr_has_maplit ts sp := 
  ⟨λte pe , timestamped_pose3d_expr.lit_time te pe⟩


class  timestamped_pose3d_expr_has_litlit {tf : time_frame_expr} (ts : time_space_expr tf)  {f : geom3d_frame_expr} (sp : geom3d_space_expr f):= 
  (cast : time ts.value → pose3d sp.value → timestamped_pose3d_expr ts sp)
notation T`↦`E := timestamped_pose3d_expr_has_litlit.cast T E
notation `|`T`,`E`|` := timestamped_pose3d_expr_has_litlit.cast T E

instance timestamped_pose3d_expr_litlit {tf : time_frame_expr} (ts : time_space_expr tf) {f : geom3d_frame_expr} (sp : geom3d_space_expr f) 
  : timestamped_pose3d_expr_has_litlit ts sp := 
  ⟨λt p , timestamped_pose3d_expr.lit_time (|t|) (|p|)⟩


variables 
 {f : geom3d_frame_expr} (sp : geom3d_space_expr f) 
  (pes : pose3d_series_expr ts sp) (te: time_expr ts) (pe:pose3d_expr sp)-- pose3d_series_expr ts sp)

#check pes[(te↦pe)]

abbreviation pose3d_series_env {tf : time_frame_expr} (ts : time_space_expr tf) {f : geom3d_frame_expr} (sp : geom3d_space_expr f) :=
  pose3d_series_var ts sp → pose3d_discrete ts.value sp.value
abbreviation pose3d_series_eval := 
            Π {tf : time_frame_expr} (ts : time_space_expr tf), 
            Π{f : geom3d_frame_expr} (sp : geom3d_space_expr f),
  pose3d_series_env ts sp → pose3d_series_expr ts sp → 
    pose3d_discrete ts.value sp.value


@[simp]
noncomputable def default_pose3d_series_env 
    {tf : time_frame_expr} (ts : time_space_expr tf) 
    {f : geom3d_frame_expr} (sp : geom3d_space_expr f) : pose3d_series_env ts sp := 
  λv, @mk_pose3d_discrete_empty tf.value ts.value f.value sp.value
    
--set_option eqn_compiler.max_steps 16384
@[simp]
noncomputable def default_pose3d_series_eval : pose3d_series_eval
:= λtf ts gf gs, λenv_, λexpr_, 
   @mk_pose3d_discrete_empty tf.value ts.value gf.value gs.value


@[simp]
noncomputable def static_pose3d_series_eval : pose3d_series_eval
| tf ts gf gs env_ (pose3d_series_expr.lit p) := p
| tf ts gf gs env_ (pose3d_series_expr.update ges te ge) :=
  ((static_pose3d_series_eval ts gs) (default_pose3d_series_env ts gs) ges)
  .update ⟨te.value,ge.value⟩
| tf ts gf gs env_ (pose3d_series_expr.update_ts ges tse) :=
  ((static_pose3d_series_eval ts gs) (default_pose3d_series_env ts gs) ges)
  .update tse.value

@[simp]
noncomputable def pose3d_series_expr.value
    {tf : time_frame_expr} {ts : time_space_expr tf} 
     {f : geom3d_frame_expr} {sp : geom3d_space_expr f} (expr_ : pose3d_series_expr ts sp)  
    : pose3d_discrete ts.value sp.value :=
  (static_pose3d_series_eval ts sp) (default_pose3d_series_env ts sp) expr_

end lang.series.geom3d
