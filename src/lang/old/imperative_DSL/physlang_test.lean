import .physlang
import .environment

/-
Test code
-/
def g1 := lang.classicalGeometry.var.mk 0
def g2 := lang.classicalGeometry.var.mk 1

--default environments
def geomDefaultEnv : environment.env := environment.env.mk
    (λ v, worldGeometry)
    (λ v, worldTime)
    (λ v, worldVelocity)
    (λ v, worldAcceleration)

def my_var : lang.classicalGeometry.var := lang.classicalGeometry.var.mk 0
def myProgram : cmd := cmd.classicalGeometryAssmt my_var (lang.classicalGeometry.expr.lit (classicalGeometry.mk 0 3))

#eval cmdEval myProgram geomDefaultEnv

