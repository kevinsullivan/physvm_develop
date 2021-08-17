import ..imperative_DSL.environment
import ..eval.axisOrientationEval

open lang.axisOrientation

def assignAxisOrientation : environment.env → orientationVar → orientationExpr → environment.env
| i v e :=
  {
    ax := ⟨(λ r,     
                if (orientationVarEq v r) 
                then (axisOrientationEval e i) 
                else (i.ax.or r))⟩
    ..i
  }