import ..imperative_DSL.environment
import ..eval.accelerationEval

open lang.classicalAcceleration

def assignAcceleration : environment.env → lang.classicalAcceleration.var → lang.classicalAcceleration.expr → environment.env
| i v e := environment.env.mk i.g i.t i.v
    (λ r,     if (varEq v r) 
        then (classicalAccelerationEval e i) 
        else (i.a r))