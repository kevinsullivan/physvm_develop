import data.real.basic
import .dimension
import ..physical_abstractions

namespace measurement

open dimension

abbreviation seconds : scale_transformation_group := ⟨1,by linarith⟩ -- ℝ is placeholder
abbreviation meters : scale_transformation_group := ⟨1,by linarith⟩ -- ℝ is placeholder

structure MeasurementSystem 
--possibly move values into type argument
:=
mk::
(time : scale_transformation_group) -- ℝ is placeholder 
(length : scale_transformation_group)


def si_standard :
  MeasurementSystem := ⟨seconds, meters⟩ 
    --seconds

end measurement