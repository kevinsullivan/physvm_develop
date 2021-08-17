import ..space_framed

namespace dimension
--TODO - REDO THIS
structure Dimension 
(length: ℚ)
(time : ℚ) := mk ::

def dim.length : Dimension 1 0 := ⟨⟩ 
def dim.time : Dimension 0 1 := ⟨⟩ 

end dimension