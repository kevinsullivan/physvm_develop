--import .expr_base
import data.real.basic
import .expr_base
import ...math.aff1Kcoord.aff1Kcoord_std


namespace lang.math

variables (K : Type*) [field K] [inhabited K] (f : fm K)

--only "one" space depends on f
structure sp_var {K : Type*} [field K] [inhabited K] (f : fm K) extends var

inductive sp_expr {K : Type*} [field K] [inhabited K] (f : fm K)
| lit (sp : spc K f) : sp_expr
| var (spv : sp_var f) : sp_expr

abbreviation sp_env {K : Type*} [field K] [inhabited K] (f : fm K) := 
  sp_var f → spc K f

abbreviation sp_eval {K : Type*} [field K] [inhabited K] (f : fm K) :=
  sp_env f → sp_expr f → spc K f

structure fm_var extends var

inductive fm_expr
| lit (f : fm K) : fm_expr
| var (spv : fm_var) : fm_expr

abbreviation fm_env :=
  fm_var → fm K

abbreviation fm_eval :=
  fm_env K → fm_expr K → fm K 

--an environment containing a frame environment depends on a frame
structure env :=
  (sp : sp_env f)
  (f : fm_env K )

def env.init : env K f  :=
  ⟨
    (λv, ⟨⟩),
    (λv, fm.base)
  ⟩

#check env.init K f

end lang.math
/-
--import .expr_base
import data.real.basic
import .expr_base
import ...math.aff1Kcoord.aff1Kcoord_std


namespace lang.math

variables (K : Type*) [field K] [inhabited K] (f : fm K)


structure sp_var extends var

inductive sp_expr
| lit (sp : spc K f) : sp_expr
| var (spv : sp_var) : sp_expr

abbreviation sp_env := 
  sp_var → spc K f

abbreviation sp_eval :=
  sp_env K f → sp_expr K f → spc K f

structure fm_var extends var

inductive fm_expr
| lit (f : fm K) : fm_expr
| var (spv : fm_var) : fm_expr

abbreviation fm_env :=
  fm_var → fm K

abbreviation fm_eval :=
  fm_env K → fm_expr K → fm K 

structure env :=
  (sp : sp_env K  f)
  (f : fm_env K )

def env.init : env K f  :=
  ⟨
    (λv, ⟨⟩),
    (λv, fm.base)
  ⟩

#check env.init K f

end lang.math-/