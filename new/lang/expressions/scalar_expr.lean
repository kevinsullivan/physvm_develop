import .expr_base
import ...phys.scalar


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

def time_scalar_expr.value
  (expr_ : scalar_expr) : scalar :=
  static_scalar_eval default_scalar_env expr_

instance : field scalar_expr := sorry
