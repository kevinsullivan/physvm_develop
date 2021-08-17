import ..imperative_DSL.environment

open lang.classicalVelocity
def classicalVelocityEval : lang.classicalVelocity.expr → environment.env → classicalVelocity 
| (expr.lit v) i := v
| (lang.classicalVelocity.expr.var v) i := i.v v
| (expr.div g t) i := 
    match g with
    | (lang.classicalGeometry.expr.lit e) := 
        match t with
        | (lang.classicalTime.expr.lit e2) := classicalVelocity.mk 0 e e2
        | (lang.classicalTime.expr.var v2) := 
            classicalVelocity.mk 0 (e) (i.t v2)
        end
    | (lang.classicalGeometry.expr.var v) := 
        match t with
        | (lang.classicalTime.expr.lit e2) := classicalVelocity.mk 0 (i.g v) (e2)
        | (lang.classicalTime.expr.var v2) := classicalVelocity.mk 0 (i.g v) (i.t v2)
        end
    end

