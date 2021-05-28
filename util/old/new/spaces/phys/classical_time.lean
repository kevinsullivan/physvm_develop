import ..affine.space_framed
import ..affine.space_standard
import .measurement
import .dimension
--import .dimension
import linear_algebra.affine_space.basic
import data.real.basic
import .phys_base
--open framed
--open standard
open measurement

namespace classical_time

universes u

variables (F : Type*) [inhabited F] [field F] 
  {T : Type*}
  [inhabited T]
  [field T] 
  [vector_space T T]
  {_f : fm F}
  {_scale : T}
  {_spc : spc F _f}

structure ClassicalTime 
  {fr : fm F} 
  extends spc F fr :=
  mk::
  (id : ℕ)

structure ClassicalTimeFrame 
  {fr : fm F}
  --{sp : spc F fr} 
  (ct : @ClassicalTime F _ _ fr)
  (m : MeasurementSystem)
  :=
  mk::

/-
structure vectr {f : fm K} (s : spc K f ) extends vec K
def mk_vectr {f : fm K} (s : spc K f ) (k : K) : vectr K s :=
vectr.mk (mk_vec K k)  

-/

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

end classical_time