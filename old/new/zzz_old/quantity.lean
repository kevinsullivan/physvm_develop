import .dimension .measurement
import ..physical_abstractions


open measurement
open dimension

variables {length : ℚ} {time : ℚ}


structure quantity (m : MeasurementSystem) (d : Dimension length time) :=
mk ::
  (val : value_isomorphism_torsor)
