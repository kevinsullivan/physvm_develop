import data.real.basic

namespace dimension
--TODO - REDO THIS
structure Dimension 
(length: ℚ)
(time : ℚ) := mk ::

--def dim.length : Dimension 1 0 := ⟨⟩ 
--def dim.time : Dimension 0 1 := ⟨⟩ 

attribute [protected]
abbreviation time := Dimension 1 0
attribute [protected]
abbreviation geom := Dimension 0 1

end dimension