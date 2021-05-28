import ..expressions.time_expr_current
open lang.time

namespace lang.time

universes u
variables {K : Type u} [field K] [inhabited K]

def env.init_env (K : Type u) [field K] [inhabited K]  : env :=
  ⟨
    (λf: fm K TIME, λsp, λv, ⟨mk_vectr sp 1⟩),
    (λf: fm K TIME, λsp, λv, ⟨mk_point sp 0⟩),
    (λf: fm K TIME, λsp1, λf2, λsp2, (λv, sp1.time_tr sp2)),
    (λv, time_std_frame K),
    (λf, (λv, mk_space K f))
  ⟩

def eval.init_eval (K : Type u) [field K] [inhabited K] : eval := 
  ⟨ 
    (λf: fm K TIME, λsp, λenv_,λexpr_, ⟨mk_vectr sp 1⟩),
    (λf: fm K TIME, λsp, λenv_,λexpr_, ⟨mk_point sp 0⟩),
    (λf: fm K TIME, λsp1, λf2, λsp2, (λenv_,λexpr_, sp1.time_tr sp2 : transform_eval sp1 sp2)),
    (λenv_, λexpr_, time_std_frame K),
    (λf, λenv_, λexpr_, mk_space K f)
  ⟩

def static_env := env.init_env
def static_eval := eval.init_eval

def time_frame_expr.value (expr_ : time_frame_expr K) : fm K TIME :=
  (static_eval K).frame (static_env K).frame expr_

def time_space_expr.value {f : fm K TIME} (expr_ : time_space_expr f)  : spc K f :=
  ((static_eval K).space f) ((static_env K).space f) expr_

def time_expr.value {f : fm K TIME} {sp : spc K f} (expr_ : time_expr sp) : time sp :=
  ((static_eval K).time sp) ((static_env K).time sp) expr_

def duration_expr.value {f : fm K TIME} {sp : spc K f} (expr_ : duration_expr sp) : duration sp :=
  ((static_eval K).duration sp) ((static_env K).duration sp) expr_

def transform_expr.value {f1 : fm K TIME} {sp1 : spc K f1} {f2 : fm K TIME} {sp2 : spc K f2}
  (expr_ : transform_expr sp1 sp2) : time_transform sp1 sp2 :=
  ((static_eval K).transform sp1 sp2) ((static_env K).transform sp1 sp2) expr_



end lang.time