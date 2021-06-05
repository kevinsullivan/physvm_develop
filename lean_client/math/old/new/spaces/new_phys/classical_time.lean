import ..space_framed
import ..space_standard
import .measurement
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


structure ClassicalTime 
  {fr : unframed.frame 1 ℝ} 
  (sp : space fr) :=
  mk::
  (id : ℕ)

structure ClassicalTimeFrame 
  (fr : unframed.frame 1 ℝ)
  {sp : space fr} 
  (ct : ClassicalTime sp)
  (m : MeasurementSystem)
  :=
  mk::

structure ClassicalTimeVector
  {fr : unframed.frame 1 ℝ}
  {sp : space fr}
  {ct : ClassicalTime sp}
  {m : MeasurementSystem}
  (f : ClassicalTimeFrame fr ct m)
  (vec : framed.framed_vector sp)
  :=
  mk::

structure ClassicalTimePoint
  {fr : unframed.frame 1 ℝ}
  {sp : space fr}
  {ct : ClassicalTime sp}
  {m : MeasurementSystem}
  (f : ClassicalTimeFrame fr ct m)
  (pt : framed.framed_point sp)
  :=
  mk::

end classical_time