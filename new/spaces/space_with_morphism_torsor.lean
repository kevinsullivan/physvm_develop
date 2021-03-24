import .affine.space_framed
import linear_algebra.affine_space.basic

open_locale affine

variables (K : Type*) [inhabited K] [field K] 
  {T : Type*}
  [inhabited T]
  [field T] 
  [vector_space T T]
  {_f : fm K}
  {_scale : T}
  {_spc : spc K _f}
/-
structure spc (f : fm K) : Type u
def mk_space (f : fm K) :=
  @spc.mk K _ _ f
-/

/-
T is a group of "scale transformations"
Actually a multiplicative torsor...group scale transformations "act" on the vectors by stretching or shrinking them coordinate-wise

This scales fine to n-dimensions
-/
instance scale_vec_torsor : add_torsor T (vectr K _spc) := sorry
instance scale_pt_torsor : add_torsor T (point K _spc) := sorry

structure fm_scaled
(f : fm K)
(scale : T) := mk :: 

instance : has_coe (fm_scaled K _f _scale) (fm K) := sorry

structure spc_scaled (f : fm_scaled K _f _scale) extends spc K (↑f)

variables (f : fm_scaled K _f _scale) (s : spc_scaled K f)

instance : has_coe (spc_scaled K f) (spc K ↑f) := sorry

structure vectr_scaled {f : fm_scaled K _f _scale} (s : spc_scaled K f) 
  extends (vectr K (↑s : spc K ↑f))

instance : has_coe (vectr_scaled K s) (vectr K (↑s : spc K ↑f))
  := ⟨λv, _scale +ᵥ v.to_vectr⟩

structure point_scaled {f : fm_scaled K _f _scale} (s : spc_scaled K f) 
  extends (point K (↑s : spc K ↑f))

instance : has_coe (point_scaled K s) (point K (↑s : spc K ↑f))
  := ⟨λv, _scale +ᵥ v.to_point⟩