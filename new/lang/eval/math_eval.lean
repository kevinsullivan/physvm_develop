import ..environment.environment

variables {K : Type*} [field K] [inhabited K]{f : fm K} (sp : spc K f)

open lang.math

namespace lang.math_eval

def fm_eval {K : Type*} [field K] [inhabited K] (f : fm K) : env K f → fm_expr K → fm K 
| e (fm_expr.lit f) := f
| e (fm_expr.var v) := e.f v


def sp_eval : env K f → sp_expr f → spc K f
| e (sp_expr.lit f) := sp
| e (sp_expr.var v) := e.sp v

end lang.math_eval