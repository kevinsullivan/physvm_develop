import ...phys.metrology.axis_orientation

namespace lang.axisOrientation
open orientation
structure var : Type :=
mk :: (num : ℕ) 

structure orientationVar extends var
inductive orientationExpr
| lit (v : AxisOrientation 3) 
| var (v : orientationVar)
abbreviation orientationEnv := orientationVar → AxisOrientation 3
abbreviation orientationEval := orientationExpr → orientationEnv → AxisOrientation 3


structure env : Type :=
(or : orientationEnv)
def orientationVarEq : orientationVar → orientationVar → bool
| v1 v2 := v1.num=v2.num
--(fr : frameEnv sp)
--(vec : vectorEnv sp)
--(pt : pointEnv sp)



noncomputable def init := λ v : orientationVar, NWU

noncomputable def initEnv : env := ⟨init⟩

end lang.axisOrientation