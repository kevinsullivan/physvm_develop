import data.real.basic
import .dimension
import ..physical_abstractions

namespace measurement

open dimension

abbreviation meters : scale_transformation_group := ⟨1,by linarith⟩ -- ℝ is placeholder
abbreviation seconds : scale_transformation_group := ⟨1,by linarith⟩ -- ℝ is placeholder

structure MeasurementSystem 
--possibly move values into type argument
:=
mk::
(length : scale_transformation_group)
(time : scale_transformation_group) -- ℝ is placeholder 


def si_standard :
  MeasurementSystem := ⟨seconds, meters⟩ 
    --seconds

end measurement