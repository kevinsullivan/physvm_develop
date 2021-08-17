import ..eval.time_eval

variables {K : Type*} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f)

open lang.time

def assign_duration : env.env K → duration_var sp → duration_expr sp →  env.env K
| i v e := 
  {
    t := {
      d := λve, if v.nm=ve.nm then ((lang.time_eval.duration_eval sp) i.t e) else i.t.d v
      ..i.t
    },
    ..i

  }

  
def assign_time : env.env K → time_var sp → @time_expr K _ _ f sp → env.env K
| i v e := 
  {
    t := {
      t := λve, if v.nm=ve.nm then ((lang.time_eval.time_eval sp) i.t e) else i.t.t v
      ..i.t
    },
    ..i
  }