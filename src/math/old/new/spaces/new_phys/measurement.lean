import data.real.basic
import .dimension

namespace measurement

open dimension

abbreviation seconds : ℝ := 1 -- ℝ is placeholder
abbreviation meters : ℝ := 1 -- ℝ is placeholder

structure MeasurementSystem 
--possibly move values into type argument
:=
mk::
(time : ℝ) -- ℝ is placeholder 


def si_standard :
  MeasurementSystem := ⟨seconds⟩ 
    --seconds

end measurement