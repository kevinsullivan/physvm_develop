import .scalar_expr
import .time_expr

namespace lang.bool_expr

open lang.time

structure bool_var extends var


inductive bool_expr
| lit (b : bool)
| btrue
| bfalse
| band 
| bor
| bnot
| scalar_lt_scalar (s1 : scalar_expr) (s2 : scalar_expr)
| duration_lt_duration {tf : time_frame_expr} {ts : time_space_expr tf} 
  (d1 : duration_expr ts) (d2 : duration_expr ts) : bool_expr

abbreviation bool_env := bool_var → bool

abbreviation bool_eval := 
  bool_env  → bool_expr → bool

def default_bool_env 
   : bool_env :=
    λv, tt

def default_bool_eval 
  : bool_eval :=
  λenv_, λexpr_, tt

def static_bool_eval 
   : bool_eval
| env_ (bool_expr.lit s) := s
| env_ (bool_expr.duration_lt_duration d1 d2) := d1.value.coord < d2.value.coord
| env_ _ := tt
--| duration_lt_duration {tf : time_frame_expr} {ts : time_space_expr tf} 
--  (d1 : duration_expr ts) (d2 : duration_expr ts) : bool_expr

def bool_expr.value
  (expr_ : bool_expr) : bool :=
  static_bool_eval default_bool_env expr_

notation `|`slit`|` := bool_expr.lit slit


notation s1<s2 := bool_expr.scalar_lt_scalar s1 s2
notation d1<d2 := bool_expr.duration_lt_duration d1 d2

inductive bool_sem : ∀ b : bool_expr, Type 1
| bool_eval_true (b : bool_expr) (is_true : b.value = tt) : bool_sem b
| bool_eval_false (b : bool_expr) (is_false : b.value = ff) : bool_sem b

meta def check_bool_true : ∀b : bool_expr,  tactic (bool_sem b)
| b := tactic.fail "wrong prop"
--| _ _ := tactic.fail "bad prop"

end lang.bool_expr