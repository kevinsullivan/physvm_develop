import ...phys.metrology.measurement

namespace lang.measurementSystem
open measurementSystem
structure var : Type :=
mk :: (num : ℕ) 

structure measureVar extends var
inductive measureExpr
| lit (v : MeasurementSystem) 
| var (v : measureVar)
abbreviation measureEnv := measureVar → MeasurementSystem
abbreviation measureEval := measureExpr → measureEnv → MeasurementSystem


structure env : Type :=
(ms : measureEnv)
def measureVarEq : measureVar → measureVar → bool
| v1 v2 := v1.num=v2.num
--(fr : frameEnv sp)
--(vec : vectorEnv sp)
--(pt : pointEnv sp)



noncomputable def init := λ v : measureVar, si_measurement_system

noncomputable def initEnv : env := ⟨init⟩

end lang.measurementSystem