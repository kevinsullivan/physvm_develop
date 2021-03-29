import ..eval.math_eval

variables {K : Type*} [field K] [inhabited K] {f : fm K} (sp : spc K f)

open lang.math

def assign_fm : @env.env K _ _ f sp → fm_var → fm_expr K  →  env.env K
| i v e := 
  {
    m := {
      f := λve, if v.nm=ve.nm then ((lang.math_eval.fm_eval f ) i.m e) else i.m.f v
      ..i.m
    },
    ..i

  }

--space not inferrable from context, so we need a space to assign a space
def assign_spc {K : Type*} [field K] [inhabited K] {f : fm K} (sp : spc K f) : @env.env K _ _ f sp → sp_var f → sp_expr f  →  env.env K
| i v e := 
  {
    m := {
      sp := λve, if v.nm=ve.nm then ((lang.math_eval.sp_eval sp) i.m e) else i.m.sp v
      ..i.m
    },
    ..i

  }
