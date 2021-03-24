import .space_framed

variables (K : Type*) [inhabited K] [field K] [vector_space K K]
  {_f : fm K}
  {_scale : K}

/-
structure spc (f : fm K) : Type u
def mk_space (f : fm K) :=
  @spc.mk K _ _ f
-/

structure fm_scaled
(f : fm K)
(scale : K) := mk :: 

instance : has_coe (fm_scaled K _f _scale) (fm K) := sorry

structure spc_scaled (f : fm_scaled K _f _scale) extends spc K (↑f)

structure vectr_scaled {f : fm_scaled K _f _scale} (s : spc_scaled K f) extends (vectr K ↑s)
