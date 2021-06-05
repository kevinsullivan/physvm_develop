import ..space_framed
import ..space_standard
import .measurement
import .dimension
--import .dimension
import linear_algebra.affine_space.basic
import data.real.basic

-- only for affine spaces!
-- R should be variable

variables {length : ℚ} {time : ℚ} {n : ℕ}

class has_dimension (T : Type*) :=
  (d : dimension.Dimension length time)

abbreviation dim := dimension.Dimension length time

open unframed
open measurement
open framed

structure PhysSpace
  {fr : unframed.frame n ℝ} 
  (sp : unframed.space n ℝ fr)
  (dim : dimension.Dimension length time) :=
  mk::
  (id : ℕ)

structure PhysFrame 
  {fr : unframed.frame n ℝ}
  {sp : unframed.space n ℝ fr} 
  {dim : dimension.Dimension length time }
  (ct : PhysSpace sp dim)
  (m : MeasurementSystem)
  :=
  mk::

structure PhysVector
  {fr : unframed.frame n ℝ}
  {sp : space n ℝ fr}
  {dim : dimension.Dimension length time }
  (ct : PhysSpace sp dim)
  {m : MeasurementSystem}
  (f : PhysFrame ct m)
  extends framed.framed_vector sp
  :=
  mk::

structure PhysPoint
  {fr : unframed.frame n ℝ}
  {sp : space n ℝ fr}
  {dim : dimension.Dimension length time }
  (ct : PhysSpace sp dim)
  {m : MeasurementSystem}
  (f : PhysFrame ct m)
  extends framed.framed_point sp
  :=
  mk::