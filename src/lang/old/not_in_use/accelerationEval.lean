import ..imperative_DSL.environment
import .geometryEval
import .timeEval

open lang.classicalAcceleration

def classicalAccelerationEval : lang.classicalAcceleration.expr → environment.env → classicalAcceleration 
| (expr.lit v) i := v
| (lang.classicalAcceleration.expr.var v) i := i.a v
| (expr.div v t) i := 
    match v with
    | (lang.classicalVelocity.expr.lit e) := 
        match t with
        | (lang.classicalTime.expr.lit e2) := classicalAcceleration.mk 0 e e2
        | (lang.classicalTime.expr.var v2) := 
            classicalAcceleration.mk 0 (e) (i.t v2)
        end
    | (lang.classicalVelocity.expr.var v) := 
        match t with
        | (lang.classicalTime.expr.lit e2) := classicalAcceleration.mk 0 (i.v v) (e2)
        | (lang.classicalTime.expr.var v2) := classicalAcceleration.mk 0 (i.v v) (i.t v2)
        end
    | (lang.classicalVelocity.expr.div g t) :=
        let G := classicalGeometryEval g i in
        let T := classicalTimeEval t i in
        classicalAcceleration.mk    
            0
            (classicalVelocity.mk 0 G T)
            T 
    end