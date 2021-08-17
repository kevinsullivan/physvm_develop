import .expr_base
import ...phys.scalar


structure scalar_var extends var

inductive scalar_expr : Type
| lit (s : scalar) : scalar_expr
| var (v : scalar_var) : scalar_expr
| add_scalar_scalar (s1 : scalar_expr) (s2 : scalar_expr) : scalar_expr
| mul_scalar_scalar (s1 : scalar_expr) (s2 : scalar_expr) : scalar_expr
| inv_scalar (s1 : scalar_expr) : scalar_expr

abbreviation scalar_env := scalar_var → scalar

abbreviation scalar_eval := 
  scalar_env  → scalar_expr → scalar

@[simp]
def default_scalar_env 
   : scalar_env :=
    λv, 1

@[simp]
def default_scalar_eval 
  : scalar_eval :=
  λenv_, λexpr_,  1

@[simp]
noncomputable def static_scalar_eval 
   : scalar_eval
| env_ (scalar_expr.lit s) := s
| env_ (scalar_expr.var v) := (env_ v)
| env_ (scalar_expr.add_scalar_scalar s1 s2) := (static_scalar_eval env_ s1) + (static_scalar_eval env_ s2)
| env_ (scalar_expr.mul_scalar_scalar s1 s2) := (static_scalar_eval env_ s1) * (static_scalar_eval env_ s2)
| env_ (scalar_expr.inv_scalar s1) := 1/(static_scalar_eval env_ s1)

@[simp]
noncomputable def scalar_expr.value
  (expr_ : scalar_expr) : scalar :=
  static_scalar_eval default_scalar_env expr_

notation `|`slit`|` := scalar_expr.lit slit

notation s1`+`s2 := scalar_expr.add_scalar_scalar s1 s2
notation s1`*`s2 := scalar_expr.mul_scalar_scalar s1 s2
notation s1`/`s2 := scalar_expr.mul_scalar_scalar s1 (scalar_expr.inv_scalar s2)
notation s1⁻¹ := scalar_expr.inv_scalar s1


structure real_scalar_var extends var

inductive real_scalar_expr : Type
| lit (s : real_scalar) : real_scalar_expr
| var (v : real_scalar_var) : real_scalar_expr
| add_real_scalar_real_scalar (s1 : real_scalar_expr) (s2 : real_scalar_expr) : real_scalar_expr
| mul_real_scalar_real_scalar (s1 : real_scalar_expr) (s2 : real_scalar_expr) : real_scalar_expr
| inv_real_scalar (s1 : real_scalar_expr) : real_scalar_expr

abbreviation real_scalar_env := real_scalar_var → real_scalar

abbreviation real_scalar_eval := 
  real_scalar_env  → real_scalar_expr → real_scalar

def default_real_scalar_env 
   : real_scalar_env :=
    λv, 1

def default_real_scalar_eval 
  : real_scalar_eval :=
  λenv_, λexpr_,  1

noncomputable def static_real_scalar_eval 
   : real_scalar_eval
| env_ (real_scalar_expr.lit s) := s
| env_ (real_scalar_expr.var v) := (env_ v)
| env_ (real_scalar_expr.add_real_scalar_real_scalar s1 s2) := (static_real_scalar_eval env_ s1) + (static_real_scalar_eval env_ s2)
| env_ (real_scalar_expr.mul_real_scalar_real_scalar s1 s2) := (static_real_scalar_eval env_ s1) * (static_real_scalar_eval env_ s2)
| env_ (real_scalar_expr.inv_real_scalar s1) := 1/(static_real_scalar_eval env_ s1)

noncomputable def real_scalar_expr.value
  (expr_ : real_scalar_expr) : real_scalar :=
  static_real_scalar_eval default_real_scalar_env expr_

notation `|`slit`|` := real_scalar_expr.lit slit

notation s1`+`s2 := real_scalar_expr.add_real_scalar_real_scalar s1 s2
notation s1`*`s2 := real_scalar_expr.mul_real_scalar_real_scalar s1 s2
notation s1`/`s2 := real_scalar_expr.mul_real_scalar_real_scalar s1 (real_scalar_expr.inv_real_scalar s2)
notation s1⁻¹ := real_scalar_expr.inv_real_scalar s1