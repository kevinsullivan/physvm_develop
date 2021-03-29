import ..environment.environment

variables {K : Type*} [field K] [inhabited K]{f : fm K} (sp : spc K f)

open lang.time

namespace lang.time_eval

def duration_eval : env sp → duration_expr sp → duration sp 
| e (duration_expr.lit f) := f
| e (duration_expr.var v) := e.d v


def time_eval : env sp  → time_expr sp → time sp
| e (time_expr.lit t) := t 
| e (time_expr.var v) := e.t v

end lang.time_eval