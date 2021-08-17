import .environment
--import ..eval.accelerationEval
--import ..eval.geometryEval
--import ..eval.timeEval
--import ..eval.velocityEval
import ..expressions.measurementSystem
import ..expressions.classical_geometry
import ..expressions.classical_time
import ..expressions.classical_hertz
import ..expressions.classical_luminous_intensity
--import ..expressions.classical_velocity
--import ..expressions.classical_acceleration
import ..override.geomOverride
import ..override.timeOverride
import ..override.hertzOverride
import ..override.luminousIntensityOverride
import ..override.measurementSystemOverride
import ..override.axisOrientationOverride
--import ..override.velocityOverride
--import ..override.accelerationOverride
import ..expressions.boolean

universes u
/-
This file implements a simple imperative mathematical physics language.
The language is in the style of Pierce's Imp but without loops for now. 
-/

inductive cmd : Type u
--| classicalGeometryAssmt (v : lang.classicalGeometry.var) (e : lang.classicalGeometry.expr) 
| skip 
| classicalTimeAssmt 
    (v : lang.classicalTime.spaceVar) 
    (e : lang.classicalTime.spaceExpr) 
| classicalTimeExpr
    (e : lang.classicalTime.spaceExpr) 
| classicalTimeFrameAssmt 
    (v : lang.classicalTime.frameVar) 
    (e : lang.classicalTime.frameExpr)
| classicalTimeFrameExpr 
    (e : lang.classicalTime.frameExpr)
| classicalTimeTransformAssmt
    (v : lang.classicalTime.transformVar)
    (e : lang.classicalTime.transformExpr)
| classicalTimeTransformExpr
    (e : lang.classicalTime.transformExpr)
| classicalTimeScalarAssmt
    (v : lang.classicalTime.ScalarVar)
    (e : lang.classicalTime.ScalarExpr)
| classicalTimeScalarExpr
    (e : lang.classicalTime.ScalarExpr)
| classicalTimeCoordinatePointAssmt 
    (v : lang.classicalTime.CoordinatePointVar) 
    (e : lang.classicalTime.CoordinatePointExpr)
| classicalTimeCoordinatePointExpr
    (e : lang.classicalTime.CoordinatePointExpr)
| classicalTimeCoordinateVectorAssmt 
    (v : lang.classicalTime.CoordinateVectorVar) 
    (e : lang.classicalTime.CoordinateVectorExpr)
| classicalTimeCoordinateVectorExpr
    (e : lang.classicalTime.CoordinateVectorExpr)
| euclideanGeometry3Assmt 
    (v : lang.euclideanGeometry3.spaceVar) 
    (e : lang.euclideanGeometry3.spaceExpr) 
| euclideanGeometry3Expr 
    (e : lang.euclideanGeometry3.spaceExpr) 
| euclideanGeometry3FrameAssmt 
    (v : lang.euclideanGeometry3.frameVar) 
    (e : lang.euclideanGeometry3.frameExpr)
| euclideanGeometry3FrameExpr 
    (e : lang.euclideanGeometry3.frameExpr)
| euclideanGeometry3TransformAssmt
    (v : lang.euclideanGeometry3.TransformVar)
    (e : lang.euclideanGeometry3.TransformExpr)
| euclideanGeometry3TransformExpr
    (e : lang.euclideanGeometry3.TransformExpr)
| euclideanGeometry3ScalarAssmt
    (v : lang.euclideanGeometry3.ScalarVar)
    (e : lang.euclideanGeometry3.ScalarExpr)
| euclideanGeometry3ScalarExpr
    (e : lang.euclideanGeometry3.ScalarExpr)
| euclideanGeometry3AngleAssmt
    (v : lang.euclideanGeometry3.AngleVar)
    (e : lang.euclideanGeometry3.AngleExpr)
| euclideanGeometry3AngleExpr
    (e : lang.euclideanGeometry3.AngleExpr)
| euclideanGeometry3OrientationAssmt
    (v : lang.euclideanGeometry3.OrientationVar)
    (e : lang.euclideanGeometry3.OrientationExpr)
| euclideanGeometry3OrientationExpr
    (e : lang.euclideanGeometry3.OrientationExpr)
| euclideanGeometry3RotationAssmt
    (v : lang.euclideanGeometry3.RotationVar)
    (e : lang.euclideanGeometry3.RotationExpr)
| euclideanGeometry3RotationExpr
    (e : lang.euclideanGeometry3.RotationExpr)
| euclideanGeometry3CoordinatePointAssmt 
    (v : lang.euclideanGeometry3.CoordinatePointVar) 
    (e : lang.euclideanGeometry3.CoordinatePointExpr)
| euclideanGeometry3CoordinatePointExpr
    (e : lang.euclideanGeometry3.CoordinatePointExpr)
| euclideanGeometry3CoordinateVectorAssmt 
    (v : lang.euclideanGeometry3.CoordinateVectorVar) 
    (e : lang.euclideanGeometry3.CoordinateVectorExpr)
| euclideanGeometry3CoordinateVectorExpr 
    (e : lang.euclideanGeometry3.CoordinateVectorExpr)
| classicalHertzAssmt 
    (v : lang.classicalHertz.spaceVar) 
    (e : lang.classicalHertz.spaceExpr) 
| classicalHertzExpr
    (e : lang.classicalHertz.spaceExpr) 
| classicalHertzQuantityAssmt
    (v : lang.classicalHertz.QuantityVar)
    (e : lang.classicalHertz.QuantityExpr)
| classicalHertzQuantityExpr
    (e : lang.classicalHertz.QuantityExpr)
| classicalLuminousIntensityAssmt 
    (v : lang.classicalLuminousIntensity.spaceVar) 
    (e : lang.classicalLuminousIntensity.spaceExpr) 
| classicalLuminousIntensityExpr
    (e : lang.classicalLuminousIntensity.spaceExpr) 
| classicalLuminousIntensityQuantityAssmt
    (v : lang.classicalLuminousIntensity.QuantityVar)
    (e : lang.classicalLuminousIntensity.QuantityExpr)
| classicalLuminousIntensityQuantityExpr
    (e : lang.classicalLuminousIntensity.QuantityExpr)
| measurementSystemAssmt 
    (v : lang.measurementSystem.measureVar) 
    (e : lang.measurementSystem.measureExpr)
| measurementSystemExpr
    (e : lang.measurementSystem.measureExpr)
| axisOrientationAssmt 
    (v : lang.axisOrientation.orientationVar) 
    (e : lang.axisOrientation.orientationExpr)
| axisOrientationExpr
    (e : lang.axisOrientation.orientationExpr)
| while 
    (b : bExpr) 
    (d : cmd) -- this is not correct and requires more careful attention
| try_catch
    (t : cmd)
    (c : cmd)
| if_then_else 
    (b : bExpr) 
    (t e : cmd)
| for 
    (b : bExpr) -- what goes here?
    (d : cmd)
    
| seq (c1 c2 : cmd)

notation one;two := cmd.seq one two
notation; := cmd.skip
notation `while `b,d := cmd.while b d
notation `try `t,`catch `c := cmd.try_catch t c
notation `for `b,d := cmd.for b d

notation v=e := cmd.classicalTimeAssmt v e
notation`expr `e := cmd.classicalTimeExpr e
notation v=e := cmd.classicalTimeFrameAssmt v e
notation`expr `e := cmd.classicalTimeFrameExpr e
notation v=e := cmd.classicalTimeTransformAssmt v e
notation`expr `e := cmd.classicalTimeTransformExpr e
notation v=e := cmd.classicalTimeScalarAssmt v e
notation`expr `e := cmd.classicalTimeScalarExpr e
notation v=e := cmd.classicalTimeCoordinatePointAssmt v e
notation`expr `e := cmd.classicalTimeCoordinatePointExpr e
notation v=e := cmd.classicalTimeCoordinateVectorAssmt v e
notation`expr `e := cmd.classicalTimeCoordinateVectorExpr e
notation v=e := cmd.euclideanGeometry3Assmt v e
notation`expr `e := cmd.euclideanGeometry3Expr e
notation v=e := cmd.euclideanGeometry3FrameAssmt v e
notation`expr `e := cmd.euclideanGeometry3FrameExpr e
notation v=e := cmd.euclideanGeometry3TransformAssmt v e
notation`expr `e := cmd.euclideanGeometry3TransformExpr e
notation v=e := cmd.euclideanGeometry3ScalarAssmt v e
notation`expr `e := cmd.euclideanGeometry3ScalarExpr e
notation v=e := cmd.euclideanGeometry3AngleAssmt v e
notation`expr `e := cmd.euclideanGeometry3AngleExpr e
notation v=e := cmd.euclideanGeometry3OrientationAssmt v e
notation`expr `e := cmd.euclideanGeometry3OrientationExpr e
notation v=e := cmd.euclideanGeometry3RotationAssmt v e
notation`expr `e := cmd.euclideanGeometry3RotationExpr e
notation v=e := cmd.euclideanGeometry3CoordinatePointAssmt v e
notation`expr `e := cmd.euclidenaGeometry3CoordinatePointExpr e
notation v=e := cmd.euclideanGeometry3CoordinateVectorAssmt v e
notation`expr `e := cmd.euclideanGeometry3CoordinateVectorExpr e
notation v=e := cmd.classicalHertzAssmt v e
notation`expr `e := cmd.classicalHertzExpr e
notation v=e := cmd.classicalHertzQuantityAssmt v e
notation `expr `e := cmd.classicalHertzQuantityExpr e
notation v=e := cmd.classicalLuminousIntensityAssmt v e
notation`expr `e := cmd.classicalLuminousIntensityExpr e
notation v=e := cmd.classicalLuminousIntensityQuantityAssmt v e
notation `expr `e := cmd.classicalLuminousIntensityQuantityExpr e
notation v=e := cmd.measurementSystemAssmt v e
notation v=e := cmd.axisOrientationAssmt v e
notation `skip` := cmd.skip


open cmd 

def cmdEval : cmd → environment.env → environment.env
/-| (classicalGeometryAssmt (v : lang.classicalGeometry.var) (e : lang.classicalGeometry.expr)) i := 
    assignGeometry i v e-/
| skip i := i
| (classicalTimeAssmt v e) i := assignTimeSpace i v e
| (classicalTimeExpr e) i := i
| (classicalTimeFrameAssmt v e) i := assignTimeFrame i v e
| (classicalTimeFrameExpr e) i := i
| (classicalTimeTransformAssmt v e) i := assignTimeTransform i v e
| (classicalTimeTransformExpr e) i := i
| (classicalTimeScalarAssmt v e) i := assignTimeScalar i v e
| (classicalTimeScalarExpr e) i := i
| (classicalTimeCoordinatePointAssmt v e) i := assignTimePoint i v e
| (classicalTimeCoordinatePointExpr e) i := i
| (classicalTimeCoordinateVectorAssmt v e) i := assignTimeVector i v e
| (classicalTimeCoordinateVectorExpr e) i := i
| (euclideanGeometry3Assmt v e) i := assignGeometry3Space i v e
| (euclideanGeometry3Expr e) i := i
| (euclideanGeometry3FrameAssmt v e) i := assignGeometry3Frame i v e
| (euclideanGeometry3FrameExpr e) i := i
| (euclideanGeometry3TransformAssmt v e) i := assignGeometry3Transform i v e
| (euclideanGeometry3TransformExpr e) i := i
| (euclideanGeometry3ScalarAssmt v e) i := assignGeometry3Scalar i v e
| (euclideanGeometry3ScalarExpr e) i := i
| (euclideanGeometry3AngleAssmt v e) i := assignGeometry3Angle i v e
| (euclideanGeometry3AngleExpr e) i := i
| (euclideanGeometry3OrientationAssmt v e) i := assignGeometry3Orientation i v e
| (euclideanGeometry3OrientationExpr e) i := i
| (euclideanGeometry3RotationAssmt v e) i := assignGeometry3Rotation i v e
| (euclideanGeometry3RotationExpr e) i := i
| (euclideanGeometry3CoordinatePointAssmt v e) i := assignGeometry3Point i v e
| (euclideanGeometry3CoordinatePointExpr e) i := i
| (euclideanGeometry3CoordinateVectorAssmt v e) i := assignGeometry3Vector i v e
| (euclideanGeometry3CoordinateVectorExpr e) i := i
| (classicalHertzAssmt v e) i := assignHertzSpace i v e
| (classicalHertzExpr e) i := i 
| (classicalHertzQuantityAssmt v e) i := assignHertzQuantity i v e
| (classicalHertzQuantityExpr e) i := i
| (classicalLuminousIntensityAssmt v e) i := assignLuminousIntensitySpace i v e
| (classicalLuminousIntensityExpr e) i := i 
| (classicalLuminousIntensityQuantityAssmt v e) i := assignLuminousIntensityQuantity i v e
| (classicalLuminousIntensityQuantityExpr e) i := i
| (measurementSystemAssmt v e) i := assignMeasurementSystem i v e
| (measurementSystemExpr e) i := i
| (axisOrientationAssmt v e) i := assignAxisOrientation i v e
| (axisOrientationExpr e) i := i
| (try_catch t c) i := i
| (cmd.while b d) i := i--cmdEval d i -- this is not correct, but this is what it is for now.
| (cmd.for b d) i := i
| (cmd.if_then_else (b : bExpr)  (t : cmd) (f : cmd)) i := i --this is also incorrect? 1/21/20
    --if (bEval b bI) then (cmdEval t i) else (cmdEval f i) - BEN AND YANNI FILL IN --1/21/20 this is somewhat trickier
| (seq (c1 : cmd) (c2 : cmd)) i0 := 
    let i1 := cmdEval c1 i0 in 
    cmdEval c2 i1
