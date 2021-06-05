import ..space_framed
import ..space_standard
import .measurement
import .dimension
--import .dimension
import linear_algebra.affine_space.basic
import data.real.basic

open framed
open standard
open measurement

namespace classical_time

--variables 
--  {t : ℝ}
--  (m : MeasurementSystem t)

abbreviation spt (fr : unframed.frame 1 ℝ) := unframed.space 1 ℝ fr


structure ClassicalTime 
  {fr : unframed.frame 1 ℝ} 
  (sp : spt fr) :=
  mk::
  (id : ℕ)

structure ClassicalTimeFrame 
  {fr : unframed.frame 1 ℝ}
  {sp : spt fr} 
  (ct : ClassicalTime sp)
  (m : MeasurementSystem)
  :=
  mk::

structure ClassicalTimeVector
  {fr : unframed.frame 1 ℝ}
  {sp : spt fr}
  {ct : ClassicalTime sp}
  {m : MeasurementSystem}
  (f : ClassicalTimeFrame ct m)
 -- (v: framed.framed_vector sp)
  :=
  mk::





structure ClassicalTimePoint
  {fr : unframed.frame 1 ℝ}
  {sp : spt fr}
  {ct : ClassicalTime sp}
  {m : MeasurementSystem}
  (f : ClassicalTimeFrame ct m)
  extends framed.framed_point sp
  :=
  mk::


variables
  {fr : unframed.frame 1 ℝ}
  {sp : spt fr}
  {ct : ClassicalTime sp}
  {m : MeasurementSystem}
  {f : ClassicalTimeFrame ct m}
  (p1 : ClassicalTimeVector f)
  (p2 : ClassicalTimeVector f)

#check p1.1 +ᵥ p2.1

end classical_time