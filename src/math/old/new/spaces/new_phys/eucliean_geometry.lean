import ..space_framed
import ..space_standard
import .measurement
--import .dimension
import linear_algebra.affine_space.basic
import data.real.basic

open framed
open standard
open measurement

namespace euclidean_geometry

--variables 
--  {t : ℝ}
--  (m : MeasurementSystem t)

variables {n : ℕ}


structure EuclideanGeometry 
  {fr : unframed.frame n ℝ} 
  extends space fr := --(sp : space fr) :=
  mk::
  (id : ℕ)

structure EuclideanGeometryFrame 
  {fr : unframed.frame n ℝ}
  --{sp : space fr} 
  (ct : @EuclideanGeometry n fr)
  (m : MeasurementSystem)
  --extends (unframed.frame n ℝ) CANNOT EXTEND INDUCTIVE
  :=
  mk::

structure EuclideanGeometryVector
  {fr : unframed.frame n ℝ}
 -- {sp : space fr}
  {ct : @EuclideanGeometry n fr}
  {m : MeasurementSystem}
  (f : EuclideanGeometryFrame ct m)
  --(vec : framed.framed_vector sp)
  extends framed.framed_vector ct.1
  :=
  mk::

structure EuclideanGeometryPoint
  {fr : unframed.frame n ℝ}
  --{sp : space fr}
  {ct : @EuclideanGeometry n fr}
  {m : MeasurementSystem}
  (f : EuclideanGeometryFrame ct m)
  --(pt : framed.framed_point sp)
  extends framed.framed_point ct.1
  :=
  mk::

noncomputable
def EuclideanGeometryFrame.Derived 
  {fr : unframed.frame n ℝ}
  --{sp : space fr}
  {eg : @EuclideanGeometry n fr}
  {m : MeasurementSystem}
  {f : EuclideanGeometryFrame eg m}
  (m1:=m)
  (origin : EuclideanGeometryPoint f)
  (basis : fin n → EuclideanGeometryVector f)
  : 
    let fr_new := unframed.mk_derived n ℝ origin.1.1 (λi, (basis i).1.1) fr in
    let sp_new : space fr := ⟨⟩ in
    let eg_new : EuclideanGeometry := ⟨sp_new, eg.2⟩ in
    EuclideanGeometryFrame eg_new m1 
  := 
    let fr_new := unframed.mk_derived n ℝ origin.1.1 (λi, (basis i).1.1) fr in
    let sp_new : space fr := ⟨⟩ in
    let eg_new : EuclideanGeometry := ⟨sp_new, eg.2⟩ in
    (⟨⟩ : EuclideanGeometryFrame eg_new m1)


end euclidean_geometry