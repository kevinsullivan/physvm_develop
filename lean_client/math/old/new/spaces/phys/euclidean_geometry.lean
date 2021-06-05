import ..space_framed
import ..space_standard
import .measurement
import .quantity
--import .dimension
import linear_algebra.affine_space.basic
import data.real.basic

open framed
open standard
open measurement

/-
Problems Encountered -
1. Extension works somewhat better than type parameters because you can "hide" framed.framed_point ct.1
from the type.

2. 
structure EuclideanGeometry 
  {fr : unframed.frame n ℝ} 
  extends space fr := --(sp : space fr) :=
  mk::
  (id : ℕ)

3. A "from_algebra" operation is still required 

  {fr : unframed.frame n ℝ}
  {sp : space fr}
  {ct : @EuclideanGeometry n fr}
  {m : MeasurementSystem}
  {f : EuclideanGeometryFrame ct m}
  (v1 : EuclideanGeometryVector f)
  (v2 : EuclideanGeometryVector f)

#check v1.1 +ᵥ v2.1

4. Coercions are buggy

instance 
  {fr : unframed.frame n ℝ}
  {sp : space fr}
  {ct : @EuclideanGeometry n fr}
  {m : MeasurementSystem}
  {f : EuclideanGeometryFrame ct m}
  {v1 : EuclideanGeometryVector f} : has_lift (EuclideanGeometryVector f) (framed.framed_vector ct.1)
  := ⟨λv,v.1⟩

instance 
  {fr : unframed.frame n ℝ}
  {sp : space fr}
  {ct : @EuclideanGeometry n fr}
  {m : MeasurementSystem}
  {f : EuclideanGeometryFrame ct m}
  {v1 : EuclideanGeometryVector f} : has_lift (framed.framed_vector ct.1) (EuclideanGeometryVector f) 
  := ⟨λv,(⟨v⟩ : EuclideanGeometryVector f)⟩


#check ((↑v1 +ᵥ v2) : EuclideanGeometryVector f)
-/

namespace euclidean_geometry

--variables 
--  {t : ℝ}
--  (m : MeasurementSystem t)

variables {n : ℕ}


structure EuclideanGeometry 
  {fr : unframed.frame n ℝ} 
  extends unframed.space n ℝ fr := --(sp : space fr) :=
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

structure EuclideanGeometryFrame' 
  {fr : unframed.frame n ℝ}
  --{sp : space fr} 
  (ct : @EuclideanGeometry n fr)
  (m : fin n → MeasurementSystem)
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

structure EuclideanGeometryQuantity
{fr : unframed.frame n ℝ}
  --{sp : space fr}
(ct : @EuclideanGeometry n fr)
(m : MeasurementSystem)
extends quantity m (dimension.dim.length)
/-
variables
  {fr : unframed.frame n ℝ}
  --{sp : space fr}
  {ct : @EuclideanGeometry n fr}
  {m : MeasurementSystem}
  {f : EuclideanGeometryFrame ct m} (p_ : framed.framed_point ct.1) (p__ : framed.framed_point ct.1)
-/
--#check p_ +ᵥ p__




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
    let sp_new : unframed.space n ℝ fr := ⟨⟩ in
    let eg_new : EuclideanGeometry := ⟨sp_new, eg.2⟩ in
    EuclideanGeometryFrame eg_new m1 
  := 
    let fr_new := unframed.mk_derived n ℝ origin.1.1 (λi, (basis i).1.1) fr in
    let sp_new : unframed.space n ℝ fr := ⟨⟩ in
    let eg_new : EuclideanGeometry := ⟨sp_new, eg.2⟩ in
    (⟨⟩ : EuclideanGeometryFrame eg_new m1)

variables
  {fr : unframed.frame n ℝ}
  {sp : unframed.space n ℝ fr}
  {ct : @EuclideanGeometry n fr}
  {m : MeasurementSystem}
  {f : EuclideanGeometryFrame ct m}
  (v1 : EuclideanGeometryVector f)
  (v2 : EuclideanGeometryVector f)
  (p1 : EuclideanGeometryPoint f)
  (p2 : EuclideanGeometryPoint f)

-- #check ((p1.algebra) +ᵥ (p2.algebra).from_algebra)

/-
instance 
  {fr : unframed.frame n ℝ}
  {sp : space fr}
  {ct : @EuclideanGeometry n fr}
  {m : MeasurementSystem}
  {f : EuclideanGeometryFrame ct m}
  {v1 : EuclideanGeometryVector f} : has_lift (EuclideanGeometryVector f) (framed.framed_vector ct.1)
  := ⟨λv,v.1⟩
-/
/-
instance 
  {fr : unframed.frame n ℝ}
  {sp : space fr}
  {ct : @EuclideanGeometry n fr}
  {m : MeasurementSystem}
  {f : EuclideanGeometryFrame ct m}
  {v1 : EuclideanGeometryVector f} : has_lift (framed.framed_vector ct.1) (EuclideanGeometryVector f) 
  := ⟨λv,(⟨v⟩ : EuclideanGeometryVector f)⟩
-/
/-
instance 
  {fr : unframed.frame n ℝ}
  {sp : space fr}
  {ct : @EuclideanGeometry n fr}
  {m : MeasurementSystem}
  {f : EuclideanGeometryFrame ct m}
  {v1 : EuclideanGeometryPoint f} : has_lift (EuclideanGeometryPoint f) (framed.framed_point ct.1)
  := ⟨λv,v.1⟩
-/
/-
instance 
  {fr : unframed.frame n ℝ}
  {sp : space fr}
  {ct : @EuclideanGeometry n fr}
  {m : MeasurementSystem}
  {f : EuclideanGeometryFrame ct m}
  {v1 : EuclideanGeometryPoint f} : has_lift (framed.framed_point ct.1) (EuclideanGeometryPoint f) 
  := ⟨λv,(⟨v⟩ : EuclideanGeometryPoint f)⟩
-/
--vec + vec

#check v1.1

#check (v1.1 : framed_point _)

#check (↑v1.1 : _)

#check (↑(v1.1) : framed_point _)

#check (↑((↑v1 : framed_point _) +ᵥ (↑v2 : framed_point _)) : EuclideanGeometryVector f)
--point + vec
#check ((↑p1 +ᵥ v1))
#check ↑p1
#check (((↑p1) +ᵥ (p1)))
-- point + point
---neg
--vec - vec


end euclidean_geometry