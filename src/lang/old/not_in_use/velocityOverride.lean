import ..imperative_DSL.environment
import ..eval.velocityEval

open lang.classicalVelocity

def assignVelocity : environment.env → lang.classicalVelocity.var → lang.classicalVelocity.expr → environment.env
| i v e := environment.env.mk i.g i.t 
    (λ r,     if (varEq v r) 
        then (classicalVelocityEval e i) 
        else (i.v r))
        i.a