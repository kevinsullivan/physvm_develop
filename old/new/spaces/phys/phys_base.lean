import ..affine.space_framed
import ..affine.space_standard
import ..space_with_morphism_torsor
import .measurement
import .dimension
--import .dimension
import linear_algebra.affine_space.basic
import data.real.basic

open measurement
open dimension

variables (length : ℚ) (time : ℚ) (dim : Dimension length time)
universes u
--variables (F : Type u) [inhabited F] [field F] (fr : fm ℝ)


/-
IN PROGRESS : Integrated "scaled components" with measurement system, 
or remove altogether and leave measurement system separate

-/


variables (F : Type*) [inhabited F] [field F] 
  {T : Type*}
  [inhabited T]
  [field T] 
  [vector_space T T]
  {_f : fm F}
  {_scale : T}
  {_spc : spc F _f}

/-

structure ClassicalTime 
  {fr : fm F} 
  extends spc F fr :=
  mk::
  (id : ℕ)


structure ClassicalTimeVector
  {fr : fm F}
  --{sp : spc F fr} 
  (ct : @ClassicalTime F _ _ fr)
  {m : MeasurementSystem}
  (f : ClassicalTimeFrame F ct m)
  extends vectr F ct.1
  :=
  mk::

structure ClassicalTimePoint
  {fr : fm F}
  --{sp : spc F fr} 
  (ct : @ClassicalTime F _ _ fr)
  {m : MeasurementSystem}
  (f : ClassicalTimeFrame F ct m)
  extends point F ct.1
  :=
  mk::

abbreviation hmm := dimension.Dimension 1 0

structure ClassicalTimeQuantity
  {fr : fm F}
  (ct : @ClassicalTime F _ _ fr)
  {m : MeasurementSystem}
  {dim : dimension.time}
  extends quantity m dim 
  := 
  mk ::


-/


/-
{fr : fm F} 
  extends spc F fr :=
  mk::
  (id : ℕ)
-/

abbreviation aff_dim := {x : Dimension length time // length=1∨time=1}
abbreviation vec_dim := {x : Dimension length time // length=1∨time=1}

/-


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

-/


structure phys_spc
  (f : fm_scaled F T _f _scale)
  (dim : aff_dim length time)
  extends spc_scaled F T f :=
  mk::
  (id : ℕ)

structure phys_fm 
  {f : fm_scaled F T _f _scale}
  {dim : aff_dim length time}
  (sp : @phys_spc length time F _ _ T _ _ _ _f _scale f dim)
  (m : MeasurementSystem) -- Measurement System should be constrained by _scale
  := mk ::


variables 
  (dim2 : aff_dim length time)
  (ff : fm_scaled F T _f _scale)
#check phys_spc length time F ff dim2


--has an implicit measurement system here. problematic or accurate?
structure classical_time
  {f : fm_scaled F T _f _scale}
  (dim : aff_dim length time)
  extends phys_spc length time F ff dim2 :=


/-
structure vectr_scaled {f : fm_scaled K _f _scale} (s : spc_scaled K f) 
  extends (vectr K (↑s : spc K ↑f))

instance : has_coe (vectr_scaled K s) (vectr K (↑s : spc K ↑f))
  := ⟨λv, _scale +ᵥ v.to_vectr⟩

structure point_scaled {f : fm_scaled K _f _scale} (s : spc_scaled K f) 
  extends (point K (↑s : spc K ↑f))

-/

#check point_scaled
/-
point_scaled :
  Π (K : Type u_3) [_inst_1 : inhabited K] [_inst_2 : field K] {T : Type u_4} 
  [_inst_3 : inhabited T]
  [_inst_4 : field T] [_inst_5 : vector_space T T] {_f : fm K} {_scale : T} 
  {f : fm_scaled K _f _scale},
    spc_scaled K f → Type u_3
-/

variables 
  (ff : fm_scaled F T _f _scale)
  {dim : aff_dim length time}
  (sp : @phys_spc length time F _ _ T  _ _ _ _f _scale ff dim)

#check @point_scaled F _ _ T _ _  _ _f _scale ff sp.1


structure phys_point 
  {f : fm_scaled F T _f _scale}
  {dim : aff_dim length time}
  (sp : @phys_spc length time F _ _ T  _ _ _ _f _scale f dim)
  {m : MeasurementSystem}
  (f : phys_fm length time F sp m)
  extends point_scaled F T sp.to_spc_scaled--@point_scaled F _ _ T _ _  _ _f _scale ff sp.1
  : Type u := mk ::

--MAY HAVE TO - NOT SURE -  
--SPLIT OUT VECTOR SPACE-ONLY VECTORS AND AFFINE SPACE-ONLY VECTORS? PROBLEM
structure phys_vectr
  {fr : fm F}
  {dim : aff_dim length time}
  {sp : @phys_spc length time F _ _ fr dim}
  {m : MeasurementSystem}
  (f : phys_fm length time F sp m)
  extends vectr F sp.1
  : Type u := mk ::

structure quantity (m : MeasurementSystem) (d : Dimension length time) :=
mk ::
  (val : value_isomorphism_torsor)
