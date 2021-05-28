import ..expressions.math_expr
import ..expressions.time_expr

namespace env

variables (K : Type*) [field K] [inhabited K]{f : fm K TIME} {sp : spc K f} 

/-
SINGLE ENVIRONMENT FOR FRAME AND SPACE
-/
structure env := 
  (t : lang.time.env sp)
  (m : @lang.math.env K _ _ f)

--env K is the type we want, not env K w x y z 
-- however, not always inferrable from context, so
def env.init : env K := 
  ⟨
    (@lang.time.env.init K _ _ f sp) ,
    @lang.math.env.init K _ _ f
  ⟩

end env

/-import ..expressions.math_expr
import ..expressions.time_expr

namespace env

variables (K : Type*) [field K] [inhabited K]{f : fm K TIME} {sp : spc K f} 

/-
SINGLE ENVIRONMENT FOR FRAME AND SPACE
-/
structure env := 
  (t : @lang.time.env K _ _ f sp)
  (m : @lang.math.env K _ _ f)

def env.init : env sp := 
  ⟨
    (@lang.time.env.init K _ _ f sp) ,
    @lang.math.env.init K _ _ f
  ⟩

end env
-/