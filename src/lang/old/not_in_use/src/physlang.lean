import .....phys.src.physlib

noncomputable theory


/-
VARIABLES
-/
mutual inductive
	PhysSpaceVar,
	EuclideanGeometry3SpaceVar,
	ClassicalTimeSpaceVar,
	ClassicalVelocity3SpaceVar,
	PhysFrameVar,
	EuclideanGeometry3FrameVar,
	ClassicalTimeFrameVar,
	ClassicalVelocity3FrameVar,
	PhysDimensionalVar,
	RealScalarVar,
	EuclideanGeometry3ScalarVar,
	ClassicalTimeScalarVar,
	ClassicalVelocity3ScalarVar,
	EuclideanGeometry3VectorVar,
	ClassicalTimeVectorVar,
	ClassicalVelocity3VectorVar,
	EuclideanGeometry3PointVar,
	ClassicalTimePointVar
with PhysSpaceVar : Type
| EuclideanGeometry3 : EuclideanGeometry3SpaceVar → PhysSpaceVar
| ClassicalTime : ClassicalTimeSpaceVar → PhysSpaceVar
| ClassicalVelocity3 : ClassicalVelocity3SpaceVar → PhysSpaceVar
with EuclideanGeometry3SpaceVar : Type
| mk : ℕ → EuclideanGeometry3SpaceVar
with ClassicalTimeSpaceVar : Type
| mk : ℕ → ClassicalTimeSpaceVar
with ClassicalVelocity3SpaceVar : Type
| mk : ℕ → ClassicalVelocity3SpaceVar
with PhysFrameVar : Type
| EuclideanGeometry3 : EuclideanGeometry3FrameVar → PhysFrameVar
| ClassicalTime : ClassicalTimeFrameVar → PhysFrameVar
| ClassicalVelocity3 : ClassicalVelocity3FrameVar → PhysFrameVar
with EuclideanGeometry3FrameVar : Type
| mk : ℕ → EuclideanGeometry3FrameVar
with ClassicalTimeFrameVar : Type
| mk : ℕ → ClassicalTimeFrameVar
with ClassicalVelocity3FrameVar : Type
| mk : ℕ → ClassicalVelocity3FrameVar
with PhysDimensionalVar : Type
| RealScalar : RealScalarVar → PhysDimensionalVar
| EuclideanGeometry3Scalar : EuclideanGeometry3ScalarVar → PhysDimensionalVar
| ClassicalTimeScalar : ClassicalTimeScalarVar → PhysDimensionalVar
| ClassicalVelocity3Scalar : ClassicalVelocity3ScalarVar → PhysDimensionalVar
| EuclideanGeometry3Vector : EuclideanGeometry3VectorVar → PhysDimensionalVar
| ClassicalTimeVector : ClassicalTimeVectorVar → PhysDimensionalVar
| ClassicalVelocity3Vector : ClassicalVelocity3VectorVar → PhysDimensionalVar
| EuclideanGeometry3Point : EuclideanGeometry3PointVar → PhysDimensionalVar
| ClassicalTimePoint : ClassicalTimePointVar → PhysDimensionalVar 
with RealScalarVar : Type 
| mk : ℕ → RealScalarVar
with EuclideanGeometry3ScalarVar : Type 
| mk : ℕ → EuclideanGeometry3ScalarVar
with ClassicalTimeScalarVar : Type 
| mk : ℕ → ClassicalTimeScalarVar
with ClassicalVelocity3ScalarVar : Type 
| mk : ℕ → ClassicalVelocity3ScalarVar
with EuclideanGeometry3VectorVar : Type 
| mk : ℕ → EuclideanGeometry3VectorVar
with ClassicalTimeVectorVar : Type 
| mk : ℕ → ClassicalTimeVectorVar
with ClassicalVelocity3VectorVar : Type 
| mk : ℕ → ClassicalVelocity3VectorVar
with EuclideanGeometry3PointVar : Type 
| mk : ℕ → EuclideanGeometry3PointVar
with ClassicalTimePointVar : Type
| mk : ℕ → ClassicalTimePointVar

/-
Physical quantity expressions
-/
mutual inductive
	--dimensionful (or less) expressions
	PhysDimensionalExpression,
	RealScalarExpression, 
	EuclideanGeometry3ScalarExpression, 
	ClassicalTimeScalarExpression, 
	ClassicalVelocity3ScalarExpression, 
	EuclideanGeometry3VectorExpression, 
	ClassicalVelocity3VectorExpression, 
	ClassicalTimeVectorExpression, 
	EuclideanGeometry3PointExpression, 
	ClassicalTimePointExpression

with PhysDimensionalExpression : Type
| RealScalar : RealScalarExpression → PhysDimensionalExpression
| EuclideanGeometry3ScalarExpression : EuclideanGeometry3ScalarExpression → PhysDimensionalExpression
| ClassicalTimeScalar : ClassicalTimeScalarExpression → PhysDimensionalExpression
| ClassicalVelocity3Scalar : ClassicalVelocity3ScalarExpression → PhysDimensionalExpression
| EuclideanGeometry3Vector : EuclideanGeometry3VectorExpression → PhysDimensionalExpression
| ClassicalTimeVector : ClassicalTimeVectorExpression → PhysDimensionalExpression
| ClassicalVelocity3Vector : ClassicalVelocity3VectorExpression → PhysDimensionalExpression
| EuclideanGeometry3Point : EuclideanGeometry3PointExpression → PhysDimensionalExpression
| ClassicalTimePoint : ClassicalTimePointExpression → PhysDimensionalExpression

with RealScalarExpression : Type
| RealLitScalar : RealScalar → RealScalarExpression
| RealVarScalar : RealScalarVar → RealScalarExpression
| RealAddScalarScalar : RealScalarExpression → RealScalarExpression → RealScalarExpression
| RealSubScalarScalar : RealScalarExpression → RealScalarExpression → RealScalarExpression
| RealMulScalarScalar : RealScalarExpression → RealScalarExpression → RealScalarExpression
| RealDivScalarScalar : RealScalarExpression → RealScalarExpression → RealScalarExpression
| RealNegScalar : RealScalarExpression → RealScalarExpression
| RealInvScalar : RealScalarExpression → RealScalarExpression
| RealParenScalar : RealScalarExpression → RealScalarExpression

with EuclideanGeometry3ScalarExpression : Type
| GeometricLitScalar : EuclideanGeometry3Scalar → EuclideanGeometry3ScalarExpression
| GeometricVarScalar : EuclideanGeometry3ScalarVar → EuclideanGeometry3ScalarExpression
| GeometricAddScalarScalar : EuclideanGeometry3ScalarExpression → EuclideanGeometry3ScalarExpression → EuclideanGeometry3ScalarExpression
| GeometricSubScalarScalar : EuclideanGeometry3ScalarExpression → EuclideanGeometry3ScalarExpression → EuclideanGeometry3ScalarExpression
| GeometricMulScalarScalar : EuclideanGeometry3ScalarExpression → EuclideanGeometry3ScalarExpression → EuclideanGeometry3ScalarExpression
| GeometricDivScalarScalar : EuclideanGeometry3ScalarExpression → EuclideanGeometry3ScalarExpression → EuclideanGeometry3ScalarExpression
| GeometricNegScalar : EuclideanGeometry3ScalarExpression → EuclideanGeometry3ScalarExpression
| GeometricInvScalar : EuclideanGeometry3ScalarExpression → EuclideanGeometry3ScalarExpression
| GeometricParenScalar : EuclideanGeometry3ScalarExpression → EuclideanGeometry3ScalarExpression
| GeometricNormVector : EuclideanGeometry3VectorExpression → EuclideanGeometry3ScalarExpression
with ClassicalTimeScalarExpression : Type
| ClassicalTimeLitScalar : ClassicalTimeScalar → ClassicalTimeScalarExpression
| ClassicalTimeVarScalar : ClassicalTimeScalarVar → ClassicalTimeScalarExpression
| ClassicalTimeAddScalarScalar : ClassicalTimeScalarExpression → ClassicalTimeScalarExpression → ClassicalTimeScalarExpression
| ClassicalTimeSubScalarScalar : ClassicalTimeScalarExpression → ClassicalTimeScalarExpression → ClassicalTimeScalarExpression
| ClassicalTimeMulScalarScalar : ClassicalTimeScalarExpression → ClassicalTimeScalarExpression → ClassicalTimeScalarExpression
| ClassicalTimeDivScalarScalar : ClassicalTimeScalarExpression → ClassicalTimeScalarExpression → ClassicalTimeScalarExpression
| ClassicalTimeNegScalar : ClassicalTimeScalarExpression → ClassicalTimeScalarExpression
| ClassicalTimeInvScalar : ClassicalTimeScalarExpression → ClassicalTimeScalarExpression
| ClassicalTimeParenScalar : ClassicalTimeScalarExpression → ClassicalTimeScalarExpression
| ClassicalTimeNormVector : ClassicalTimeVectorExpression → ClassicalTimeScalarExpression
with ClassicalVelocity3ScalarExpression : Type
| VelocityLitScalar : ClassicalVelocity3Scalar → ClassicalVelocity3ScalarExpression 
| VelocityVarScalar : ClassicalVelocity3ScalarVar → ClassicalVelocity3ScalarExpression
| VelocityAddScalarScalar : ClassicalVelocity3ScalarExpression → ClassicalVelocity3ScalarExpression → ClassicalVelocity3ScalarExpression 
| VelocitySubScalarScalar : ClassicalVelocity3ScalarExpression → ClassicalVelocity3ScalarExpression → ClassicalVelocity3ScalarExpression
| VelocityMulScalarScalar : ClassicalVelocity3ScalarExpression → ClassicalVelocity3ScalarExpression → ClassicalVelocity3ScalarExpression
| VelocityDivScalarScalar : ClassicalVelocity3ScalarExpression → ClassicalVelocity3ScalarExpression → ClassicalVelocity3ScalarExpression
| VelocityNegScalar : ClassicalVelocity3ScalarExpression → ClassicalVelocity3ScalarExpression
| VelocityInvScalar : ClassicalVelocity3ScalarExpression → ClassicalVelocity3ScalarExpression
| VelocityParenScalar : ClassicalVelocity3ScalarExpression → ClassicalVelocity3ScalarExpression
| VelocityNormVector : ClassicalVelocity3VectorExpression → ClassicalVelocity3ScalarExpression
with EuclideanGeometry3VectorExpression : Type
| EuclideanGeometry3LitVector (sp : EuclideanGeometrySpace 3) : EuclideanGeometryVector sp → EuclideanGeometry3VectorExpression
| EuclideanGeometry3VarVector : EuclideanGeometry3VectorVar → EuclideanGeometry3VectorExpression
| EuclideanGeometry3AddVectorVector : EuclideanGeometry3VectorExpression → EuclideanGeometry3VectorExpression → EuclideanGeometry3VectorExpression
| EuclideanGeometry3NegVector : EuclideanGeometry3VectorExpression → EuclideanGeometry3VectorExpression
| EuclideanGeometry3MulScalarVector : RealScalarExpression → EuclideanGeometry3VectorExpression → EuclideanGeometry3VectorExpression
| EuclideanGeometry3MulVectorScalar : EuclideanGeometry3VectorExpression → RealScalarExpression → EuclideanGeometry3VectorExpression
| EuclideanGeometry3SubPointPoint : EuclideanGeometry3PointExpression → EuclideanGeometry3PointExpression → EuclideanGeometry3VectorExpression
| EuclideanGeometry3ParenVector : EuclideanGeometry3VectorExpression → EuclideanGeometry3VectorExpression
| EuclideanGeometry3CoordVector : EuclideanGeometry3ScalarExpression → EuclideanGeometry3ScalarExpression → EuclideanGeometry3ScalarExpression → EuclideanGeometry3VectorExpression
with ClassicalVelocity3VectorExpression : Type
| ClassicalVelocity3LitVector (sp : ClassicalVelocitySpace 3) :  ClassicalVelocityVector sp → ClassicalVelocity3VectorExpression
| ClassicalVelocity3VarVector : ClassicalVelocity3VectorVar → ClassicalVelocity3VectorExpression
| ClassicalVelocity3AddVectorVector : ClassicalVelocity3VectorExpression → ClassicalVelocity3VectorExpression → ClassicalVelocity3VectorExpression
| ClassicalVelocity3NegVector : ClassicalVelocity3VectorExpression → ClassicalVelocity3VectorExpression
| ClassicalVelocity3MulScalarVector : RealScalarExpression → ClassicalVelocity3VectorExpression → ClassicalVelocity3VectorExpression
| ClassicalVelocity3MulVectorScalar : ClassicalVelocity3VectorExpression → RealScalarExpression → ClassicalVelocity3VectorExpression
| ClassicalVelocity3ParenVector : ClassicalVelocity3VectorExpression  → ClassicalVelocity3VectorExpression
| ClassicalVelocity3CoordVector : ClassicalVelocity3ScalarExpression → ClassicalVelocity3ScalarExpression → ClassicalVelocity3ScalarExpression → ClassicalVelocity3VectorExpression
with ClassicalTimeVectorExpression : Type
| ClassicalTimeLitVector (sp : ClassicalTimeSpace) : ClassicalTimeVector sp → ClassicalTimeVectorExpression
| ClassicalTimeVarVector : ClassicalTimeVectorVar → ClassicalTimeVectorExpression
| ClassicalTimeAddVectorVector : ClassicalTimeVectorExpression → ClassicalTimeVectorExpression → ClassicalTimeVectorExpression
| ClassicalTimeNegVector : ClassicalTimeVectorExpression → ClassicalTimeVectorExpression
| ClassicalTimeMulScalarVector : RealScalarExpression → ClassicalTimeVectorExpression → ClassicalTimeVectorExpression
| ClassicalTimeMulVectorScalar : ClassicalTimeVectorExpression → RealScalarExpression → ClassicalTimeVectorExpression 
| ClassicalTimeSubPointPoint : ClassicalTimePointExpression → ClassicalTimePointExpression → ClassicalTimeVectorExpression
| ClassicalTimeParenVector : ClassicalTimeVectorExpression → ClassicalTimeVectorExpression
| ClassicalTimeCoordVector : ClassicalTimeScalarExpression → ClassicalTimeVectorExpression
with EuclideanGeometry3PointExpression : Type
| EuclideanGeometry3LitPoint (sp : EuclideanGeometrySpace 3) : EuclideanGeometryPoint sp → EuclideanGeometry3PointExpression
| EuclideanGeometry3VarPoint : EuclideanGeometry3PointVar → EuclideanGeometry3PointExpression
| EuclideanGeometry3SubVectorVector : EuclideanGeometry3VectorExpression → EuclideanGeometry3VectorExpression → EuclideanGeometry3PointExpression
| EuclideanGeometry3NegPoint : EuclideanGeometry3PointExpression → EuclideanGeometry3PointExpression
| EuclideanGeometry3AddPointVector : EuclideanGeometry3PointExpression → EuclideanGeometry3VectorExpression → EuclideanGeometry3PointExpression
| EuclideanGeometry3AddVectorPoint : EuclideanGeometry3VectorExpression → EuclideanGeometry3PointExpression → EuclideanGeometry3PointExpression
| EuclideanGeometry3ScalarPoint : RealScalarExpression → EuclideanGeometry3PointExpression → EuclideanGeometry3PointExpression
| EuclideanGeometry3PointScalar : EuclideanGeometry3PointExpression → RealScalarExpression → EuclideanGeometry3PointExpression
| EuclideanGeometry3ParenPoint : EuclideanGeometry3PointExpression → EuclideanGeometry3PointExpression
| EuclideanGeometry3CoordPoint : EuclideanGeometry3ScalarExpression → EuclideanGeometry3ScalarExpression → EuclideanGeometry3ScalarExpression → EuclideanGeometry3PointExpression
with ClassicalTimePointExpression : Type
|ClassicalTimeLitPoint (sp : ClassicalTimeSpace) : ClassicalTimePoint sp →ClassicalTimePointExpression
|ClassicalTimeVarPoint :ClassicalTimePointVar →ClassicalTimePointExpression
|ClassicalTimeSubVectorVector :ClassicalTimeVectorExpression →ClassicalTimeVectorExpression →ClassicalTimePointExpression
|ClassicalTimeNegPoint :ClassicalTimePointExpression →ClassicalTimePointExpression
|ClassicalTimeAddPointVector :ClassicalTimePointExpression →ClassicalTimeVectorExpression →ClassicalTimePointExpression
|ClassicalTimeAddVectorPoint :ClassicalTimeVectorExpression →ClassicalTimePointExpression →ClassicalTimePointExpression
|ClassicalTimeScalarPoint : RealScalarExpression →ClassicalTimePointExpression →ClassicalTimePointExpression
|ClassicalTimePointScalar :ClassicalTimePointExpression → RealScalarExpression →ClassicalTimePointExpression
|ClassicalTimeParenPoint :ClassicalTimePointExpression →ClassicalTimePointExpression
|ClassicalTimeCoordPoint : ClassicalTimeScalarExpression →ClassicalTimePointExpression

/-
Space and frame expressions
-/
mutual inductive
	PhysSpaceExpression,
	PhysFrameExpression,
	EuclideanGeometry3SpaceExpression,
	ClassicalTimeSpaceExpression,
	ClassicalVelocity3SpaceExpression,
	EuclideanGeometry3FrameExpression,
	ClassicalTimeFrameExpression,
	ClassicalVelocity3FrameExpression
with PhysSpaceExpression : Type
| EuclideanGeometry3Expr : EuclideanGeometry3SpaceExpression → PhysSpaceExpression
| ClassicalTimeExpr : ClassicalTimeSpaceExpression → PhysSpaceExpression
| ClassicalVelocity3Expr : ClassicalVelocity3SpaceExpression → PhysSpaceExpression
| Var : PhysSpaceVar → PhysSpaceExpression 
with PhysFrameExpression :  Type
| EuclideanGeometry3FrameExpr : EuclideanGeometry3FrameExpression → PhysFrameExpression
| ClassicalTimeFrameExpr : ClassicalTimeFrameExpression → PhysFrameExpression
| ClassicalVelocity3FrameExpr : ClassicalVelocity3FrameExpression → PhysFrameExpression
| Var : PhysFrameVar → PhysFrameExpression
with EuclideanGeometry3SpaceExpression: Type
| EuclideanGeometry3Literal (sp : EuclideanGeometrySpace 3) : EuclideanGeometry3SpaceExpression
with ClassicalTimeSpaceExpression: Type
| ClassicalTimeLiteral : ClassicalTimeSpace → ClassicalTimeSpaceExpression
with ClassicalVelocity3SpaceExpression : Type
| ClassicalVelocity3Literal : ClassicalVelocitySpace 3 → ClassicalVelocity3SpaceExpression
with EuclideanGeometry3FrameExpression: Type
| FrameLiteral {sp : EuclideanGeometrySpace 3} : EuclideanGeometryFrame sp → EuclideanGeometry3FrameExpression
with ClassicalTimeFrameExpression: Type
| FrameLiteral {sp : ClassicalTimeSpace} : ClassicalTimeFrame sp → ClassicalTimeFrameExpression
with ClassicalVelocity3FrameExpression : Type
| FrameLiteral {sp : ClassicalVelocitySpace 3} : ClassicalVelocityFrame sp → ClassicalVelocity3FrameExpression

inductive PhysBooleanExpression : Type
| BooleanTrue : PhysBooleanExpression
| BooleanFalse : PhysBooleanExpression
| BooleanAnd : PhysBooleanExpression → PhysBooleanExpression → PhysBooleanExpression
| BooleanOr : PhysBooleanExpression → PhysBooleanExpression → PhysBooleanExpression
| BooleanNot : PhysBooleanExpression → PhysBooleanExpression
-- A LARGE NUMBER OF SCALAR AND VECTOR INEQUALITIES BELONG HERE

/-
KEVIN: These are kinds of thoughts we want to be able to express when annotating code:
var geom := GeometricEuclideanSpace("World geometry",3)
var stdGeomFrame := geom.stdFrame()
var stdGeomOrigin := stdGeomFrame.origin();
-/

/-
Imperative top-level DSL syntax
-/
inductive PhysCommand : Type
| SpaceAssignment : PhysSpaceVar → PhysSpaceExpression → PhysCommand
| FrameAssignment : PhysFrameVar → PhysFrameExpression → PhysCommand
| Assignment : PhysDimensionalVar → PhysDimensionalExpression → PhysCommand
| While : PhysBooleanExpression → PhysCommand → PhysCommand
| IfThenElse : PhysBooleanExpression → PhysCommand → PhysCommand → PhysCommand
| Seq : PhysCommand → PhysCommand → PhysCommand 
| CmdExpr : PhysDimensionalExpression → PhysCommand


/-
NOTATIONS BEGIN HERE
--7/16 (7/15) - OUR MAGIC NOTATION CANDIDATE LIST:
--https://www.caam.rice.edu/~heinken/latex/symbols.pdf
-/

notation !n := EuclideanGeometry3SpaceVar.mk n
notation !n := ClassicalTimeSpaceVar.mk n
notation !n := ClassicalVelocity3SpaceVar.mk n
notation !n := EuclideanGeometry3FrameVar.mk n
notation !n := ClassicalTimeFrameVar.mk n
notation !n := ClassicalVelocity3FrameVar.mk n
notation !n := RealScalarVar.mk n
notation !n := EuclideanGeometry3ScalarVar.mk n
notation !n := ClassicalTimeScalarVar.mk n
notation !n := ClassicalVelocity3ScalarVar.mk n
notation !n := EuclideanGeometry3VectorVar.mk n
notation !n := ClassicalTimeVectorVar.mk n
notation !n := ClassicalVelocity3VectorVar.mk n
notation !n := EuclideanGeometry3PointVar.mk n
notation !n := ClassicalTimePointVar.mk n

notation ?e := PhysSpaceVar.EuclideanGeometryLiteral e
notation ?e := PhysSpaceVar.ClassicalTimeLiteral e
notation ?e := PhysSpaceVar.ClassicalVelocityLiteral 3

notation a=b := PhysCommand.Assignment a b
notation a=b := PhysCommand.SpaceAssignment a b
notation a=b := PhysCommand.FrameAssignment a b

notation ⊢e := PhysDimensionalVar.RealScalar e
notation ⊢e := PhysDimensionalVar.EuclideanGeometry3Scalar e
notation ⊢e := PhysDimensionalVar.ClassicalTimeScalar e
notation ⊢e := PhysDimensionalVar.ClassicalVelocity3Scalar e
notation ⊢e := PhysDimensionalVar.EuclideanGeometry3Vector e
notation ⊢e := PhysDimensionalVar.ClassicalTimeVector e
notation ⊢e := PhysDimensionalVar.ClassicalVelocity3Vector e
notation ⊢e := PhysDimensionalVar.EuclideanGeometry3Point e
notation ⊢e := PhysDimensionalVar.ClassicalTimePoint e

notation ⊢e := PhysDimensionalExpression.RealScalarExpression e
notation ⊢e := PhysDimensionalExpression.EuclideanGeometry3Scalar e
notation ⊢e := PhysDimensionalExpression.ClassicalTimeScalar e
notation ⊢e := PhysDimensionalExpression.ClassicalVelocity3Scalar e
notation ⊢e := PhysDimensionalExpression.EuclideanGeometry3Vector e
notation ⊢e := PhysDimensionalExpression.ClassicalTimeVector e
notation ⊢e := PhysDimensionalExpression.ClassicalVelocity3Vector e
notation ⊢e := PhysDimensionalExpression.EuclideanGeometry3Point e
notation ⊢e := PhysDimensionalExpression.ClassicalTimePoint e


notation ⊢v := PhysSpaceVar.ClassicalTime v
notation ⊢v := PhysSpaceVar.ClassicalVelocity3 v
notation ⊢v := PhysSpaceVar.EuclideanGeometry3 v
notation ⊢e := PhysSpaceExpression.ClassicalTimeExpr e
notation ⊢e := PhysSpaceExpression.ClassicalVelocity3Expr e
notation ⊢e := PhysSpaceExpression.EuclideanGeometry3Expr e


notation ⊢v := PhysFrameVar.ClassicalTime v
notation ⊢v := PhysFrameVar.ClassicalVelocity3 v
notation ⊢v := PhysFrameVar.EuclideanGeometry3 v
notation ⊢e := PhysFrameExpression.ClassicalTimeFrameExpr e
notation ⊢e := PhysFrameExpression.ClassicalVelocity3FrameExpr e
notation ⊢e := PhysFrameExpression.EuclideanGeometry3FrameExpr e

notation !n := RealScalarVar.mk n
notation !n := EuclideanGeometry3ScalarVar.mk n
notation !n := ClassicalTimeScalarVar.mk n
notation !n := ClassicalVelocity3ScalarVar.mk n
notation !n := EuclideanGeometry3VectorVar.mk n
notation !n := ClassicalTimeVectorVar.mk n
notation !n := ClassicalVelocity3VectorVar.mk n
notation !n := EuclideanGeometry3PointVar.mk n
notation !n := ClassicalTimePointVar.mk n

--RealScalarExpression Notations
notation %e := RealScalarExpression.RealVarScalar e
instance : has_add RealScalarExpression := ⟨RealScalarExpression.RealAddScalarScalar⟩ 
notation e1 - e2 := RealScalarExpression.RealSubScalarScalar e1 e2
notation e1 ⬝ e2 := RealScalarExpression.RealMulScalarScalar e1 e2
notation e1 / e2 := RealScalarExpression.RealDivScalarScalar e1 e2
instance : has_neg RealScalarExpression := ⟨RealScalarExpression.RealNegScalar⟩ 
notation e⁻¹ := RealScalarExpression.RealInvScalar e
notation $e := RealScalarExpression.RealParenScalar e
notation ⬝e := RealScalarExpression.RealLitScalar e

--EuclideanGeometry3ScalarExpression Notations
notation %e := EuclideanGeometry3ScalarExpression.GeometricVarScalar e
instance : has_add EuclideanGeometry3ScalarExpression := ⟨EuclideanGeometry3ScalarExpression.GeometricAddScalarScalar⟩ 
notation e1 - e2 := EuclideanGeometry3ScalarExpression.GeometricSubScalarScalar e1 e2
notation e1 ⬝ e2 := EuclideanGeometry3ScalarExpression.GeometricMulScalarScalar e1 e2
notation e1 / e2 := EuclideanGeometry3ScalarExpression.GeometricDivScalarScalar e1 e2
instance : has_neg EuclideanGeometry3ScalarExpression := ⟨EuclideanGeometry3ScalarExpression.GeometricNegScalar⟩  
notation e⁻¹ := EuclideanGeometry3ScalarExpression.GeometricInvScalar e
notation $e := EuclideanGeometry3ScalarExpression.GeometricParenScalar e
notation |e| := EuclideanGeometry3ScalarExpression.GeometricNormVector e
notation ⬝e := EuclideanGeometry3ScalarExpression.GeometricLitScalar e


--ClassicalTimeScalarExpression Notations
notation %e := ClassicalTimeScalarExpression.ClassicalTimeVarScalar  
instance : has_add ClassicalTimeScalarExpression := ⟨ClassicalTimeScalarExpression.ClassicalTimeAddScalarScalar⟩ 
notation e1 - e2 := ClassicalTimeScalarExpression.ClassicalTimeSubScalarScalar e1 e2
notation e1 ⬝ e2 := ClassicalTimeScalarExpression.ClassicalTimeMulScalarScalar e1 e2
notation e1 / e2 := ClassicalTimeScalarExpression.ClassicalTimeDivScalarScalar e1 e2
instance : has_neg ClassicalTimeScalarExpression := ⟨ClassicalTimeScalarExpression.ClassicalTimeNegScalar⟩ 
notation e⁻¹ := ClassicalTimeScalarExpression.ClassicalTimeInvScalar e
notation $e := ClassicalTimeScalarExpression.ClassicalTimeParenScalar e
notation |e| := ClassicalTimeScalarExpression.ClassicalTimeNormVector e
notation ⬝e := ClassicalTimeScalarExpression.ClassicalTimeLitScalar e


--ClassicalVelocity3ScalarExpression Notations
notation %e := ClassicalVelocity3ScalarExpression.VelocityVarScalar e
instance : has_add ClassicalVelocity3ScalarExpression := ⟨ClassicalVelocity3ScalarExpression.VelocityAddScalarScalar⟩ 
notation e1 - e2 := ClassicalVelocity3ScalarExpression.VelocitySubScalarScalar e1 e2
notation e1 ⬝ e2 := ClassicalVelocity3ScalarExpression.VelocityMulScalarScalar e1 e2
notation e1 / e2 := ClassicalVelocity3ScalarExpression.VelocityDivScalarScalar e1 e2
instance : has_neg ClassicalVelocity3ScalarExpression := ⟨ClassicalVelocity3ScalarExpression.VelocityNegScalar⟩ 
notation e⁻¹ := ClassicalVelocity3ScalarExpression.VelocityInvScalar e
notation $e := ClassicalVelocity3ScalarExpression.VelocityParenScalar e
notation |e| := ClassicalVelocity3ScalarExpression.VelocityNormVector e
notation ⬝e := ClassicalVelocity3ScalarExpression.VelocityLitScalar e


--Geometric3Vector Notations
notation %e := EuclideanGeometry3VectorExpression.EuclideanGeometry3VarVector e
instance : has_add EuclideanGeometry3VectorExpression := ⟨EuclideanGeometry3VectorExpression.EuclideanGeometry3AddVectorVector⟩ 
instance : has_neg EuclideanGeometry3VectorExpression := ⟨EuclideanGeometry3VectorExpression.EuclideanGeometry3NegVector⟩ 
notation c ⬝ e := EuclideanGeometry3VectorExpression.EuclideanGeometry3MulScalarVector c e
notation e ⬝ c := EuclideanGeometry3VectorExpression.EuclideanGeometry3MulVectorScalar e c
notation e1 - e2 := EuclideanGeometry3VectorExpression.EuclideanGeometry3SubPointPoint e1 e2
notation $e := EuclideanGeometry3VectorExpression.EuclideanGeometry3ParenVector e
notation ~e := EuclideanGeometry3VectorExpression.EuclideanGeometry3LitVector e
notation e1⬝e2⬝e3 := EuclideanGeometry3VectorExpression.EuclideanGeometry3CoordVector e1 e2 e3


--ClassicalVelocity3Vector Notations
notation %e := ClassicalVelocity3VectorExpression.ClassicalVelocity3VarVector e
instance : has_add ClassicalVelocity3VectorExpression := ⟨ClassicalVelocity3VectorExpression.ClassicalVelocity3AddVectorVector⟩ 
instance : has_neg ClassicalVelocity3VectorExpression := ⟨ClassicalVelocity3VectorExpression.ClassicalVelocity3NegVector⟩ 
notation c ⬝ e := ClassicalVelocity3VectorExpression.ClassicalVelocity3MulScalarVector c e
notation e ⬝ c := ClassicalVelocity3VectorExpression.ClassicalVelocity3MulVectorScalar e c
notation e1 - e2 := ClassicalVelocity3VectorExpression.ClassicalVelocity3SubPointPoint e1 e2
notation $e := ClassicalVelocity3VectorExpression.ClassicalVelocity3ParenVector e
notation ~e := ClassicalVelocity3VectorExpression.ClassicalVelocity3LitVector e
notation e1⬝e2⬝e3 := ClassicalVelocity3VectorExpression.ClassicalVelocity3CoordVector e1 e2 e3


--ClassicalTimeVector Notations
notation %e := ClassicalTimeVectorExpression.ClassicalTimeVarVector e
instance : has_add ClassicalTimeVectorExpression := ⟨ClassicalTimeVectorExpression.ClassicalTimeAddVectorVector⟩ 
instance : has_neg ClassicalTimeVectorExpression := ⟨ClassicalTimeVectorExpression.ClassicalTimeNegVector⟩ 
notation c⬝e := ClassicalTimeVectorExpression.ClassicalTimeMulScalarVector c e
notation e⬝c := ClassicalTimeVectorExpression.ClassicalTimeMulVectorScalar e c
notation e1-e2 := ClassicalTimeVectorExpression.ClassicalTimeSubPointPoint e1 e2
notation $e := ClassicalTimeVectorExpression.ClassicalTimeParenVector e
notation ~e := ClassicalTimeVectorExpression.ClassicalTimeLitVector e
notation ⬝e := ClassicalTimeVectorExpression.ClassicalTimeCoordVector e


--EuclideanGeometry3Point Notations
notation %e := EuclideanGeometry3PointExpression.EuclideanGeometry3VarPoint e
notation e1 - e2 := EuclideanGeometry3PointExpression.EuclideanGeometry3SubVectorVector e1 e2
instance : has_neg EuclideanGeometry3PointExpression := ⟨EuclideanGeometry3PointExpression.EuclideanGeometry3NegPoint⟩
instance : has_trans EuclideanGeometry3VectorExpression EuclideanGeometry3PointExpression  := ⟨EuclideanGeometry3PointExpression.EuclideanGeometry3AddVectorPoint⟩
notation c • e := EuclideanGeometry3PointExpression.EuclideanGeometry3ScalarPoint c e
notation e • c := EuclideanGeometry3PointExpression.EuclideanGeometry3PointScalar e c
notation $e := EuclideanGeometry3PointExpression.EuclideanGeometry3ParenPoint e
notation ~e := EuclideanGeometry3PointExpression.EuclideanGeometry3LitPoint e
notation e1⬝e2⬝e3 := EuclideanGeometry3PointExpression.EuclideanGeometry3CoordPoint e1 e2 e3

--ClassicalTimePoint Notations
notation %e := ClassicalTimePointExpression.ClassicalTimeVarPoint e
notation e1 ⊹ e2 := ClassicalTimePointExpression.ClassicalTimeAddPointVector e1 e2
instance : has_trans ClassicalTimeVectorExpression ClassicalTimePointExpression  := ⟨ClassicalTimePointExpression.ClassicalTimeAddVectorPoint⟩
notation $e := ClassicalTimePointExpression.ClassicalTimeParenPoint e
notation e1 - e2 := ClassicalTimePointExpression.ClassicalTimeSubVectorVector e1 e2
instance : has_neg ClassicalTimePointExpression := ⟨ClassicalTimePointExpression.ClassicalTimeNegPoint⟩ 
notation c • e := ClassicalTimePointExpression.ClassicalTimeScalarPoint c e
notation e • c := ClassicalTimePointExpression.ClassicalTimePointScalar e c
notation ~e := ClassicalTimePointExpression.ClassicalTimeLitPoint e
notation ⬝e := ClassicalTimePointExpression.ClassicalTimeCoordPoint e

abbreviation RealScalarInterp := RealScalarVar → RealScalar
--abbreviation EuclideanGeometryScalarInterp := EuclideanGeometry3ScalarVar → EuclideanGeometryScalar
--abbreviation ClassicalTimeScalarInterp := ClassicalTimeScalarVar → ClassicalTimeScalar
--abbreviation ClassicalVelocityScalarInterp := ClassicalVelocity3ScalarVar → ClassicalVelocityScalar

abbreviation EuclideanGeometry3ScalarInterp := EuclideanGeometry3ScalarVar → EuclideanGeometry3Scalar
abbreviation ClassicalTimeScalarInterp := ClassicalTimeScalarVar → ClassicalTimeScalar
abbreviation ClassicalVelocity3ScalarInterp := ClassicalVelocity3ScalarVar → ClassicalVelocity3Scalar

abbreviation EuclideanGeometry3VectorInterp (sp : EuclideanGeometrySpace 3) := EuclideanGeometry3VectorVar → EuclideanGeometryVector sp
abbreviation ClassicalTimeVectorInterp (sp : ClassicalTimeSpace) := ClassicalTimeVectorVar → ClassicalTimeVector sp
abbreviation ClassicalVelocity3VectorInterp (sp : ClassicalVelocitySpace 3):= ClassicalVelocity3VectorVar → ClassicalVelocityVector sp

abbreviation EuclideanGeometry3PointInterp (sp : EuclideanGeometrySpace 3):= EuclideanGeometry3PointVar → EuclideanGeometryPoint sp
abbreviation ClassicalTimePointInterp (sp : ClassicalTimeSpace) := ClassicalTimePointVar → ClassicalTimePoint sp
--abbreviation ClassicalVelocity3PointInterp := ClassicalVelocity3PointVar → ClassicalVelocity3PointStruct

def DefaultRealScalarInterp : RealScalarInterp := λ scalar, RealScalarDefault

/-
EVALUATION / SEMANTICS?
-/

def EvalEuclideanGeometry3SpaceExpression : EuclideanGeometry3SpaceExpression → EuclideanGeometrySpace 3
| (EuclideanGeometry3SpaceExpression.EuclideanGeometry3Literal sp) := sp
def EvalClassicalVelocity3SpaceExpression : ClassicalVelocity3SpaceExpression → ClassicalVelocitySpace 3
| (ClassicalVelocity3SpaceExpression.ClassicalVelocity3Literal sp) := sp
def EvalClassicalTimeSpaceExpression : ClassicalTimeSpaceExpression → ClassicalTimeSpace
| (ClassicalTimeSpaceExpression.ClassicalTimeLiteral sp) := sp

/-
OLD COMMENTS BELOW, SAVED FOR NOW
-/

/-
-- Imperative top-level DSL syntax

mutual inductive
	PhysProgram,
	PhysFunction,
	PhysGlobalCommand,
	PhysCommand
	
with PhysProgram : Type
| Program : PhysGlobalCommand → PhysProgram
with PhysFunction : Type
| DeclareFunction : PhysCommand → PhysFunction 
with PhysGlobalCommand : Type
| Seq : list PhysGlobalCommand → PhysGlobalCommand
| GlobalSpace : PhysSpaceVar → PhysSpaceExpression → PhysGlobalCommand
| GlobalFrame : PhysFrameVar → PhysFrameExpression → PhysGlobalCommand
| Function : PhysCommand → PhysGlobalCommand
| Main : PhysCommand → PhysGlobalCommand
with PhysCommand : Type
| Seq : list PhysCommand → PhysCommand
--| Block : PhysCommand → PhysCommand
| While : PhysBooleanExpression → PhysCommand → PhysCommand
| IfThenElse : PhysBooleanExpression → PhysCommand → PhysCommand → PhysCommand
| Assignment : PhysDimensionalVar → PhysDimensionalExpression → PhysCommand
--| Expression : PhysDimensionalExpression
-/



/-
What exactly does the DSL instance look like for our 0-line program

def BuildEuclideanGeometry3Space : EuclideanGeometrySpace 3 := 
    EuclideanGeometrySpace.SpaceLiteral 3 (PhysAffineSpace.SpaceLiteral 3 meters si_standard) <needs to be connected to mathlib>

def x := PhysSpaceVar.mk 1
def y := PhysSpaceExpression.SpaceLiteral <a physlib object> 
def z := PhysGlobalCommand.GlobalSpace x y
def a := PhysGlobalCommand.Seq z

def prog := PhysProgram z 
OR
def prog := PhysProgram a
OR
def prog := a

def := PhysGlobalGlobal 

def X : EuclideanGeometry3ScalarExpression := EuclideanGeometry3ScalarExpression.GeometricLitScalar (EuclideanGeometry3Scalar.mk 0 meters)
def Y : EuclideanGeometry3ScalarExpression := EuclideanGeometry3ScalarExpression.GeometricLitScalar (EuclideanGeometry3Scalar.mk 0 meters)
def Z : EuclideanGeometry3ScalarExpression := EuclideanGeometry3ScalarExpression.GeometricLitScalar (EuclideanGeometry3Scalar.mk 0 meters)
def R : RealScalarExpression := RealScalarExpression.RealLitScalar RealScalarDefault
def geomexpr : EuclideanGeometry3VectorExpression := EuclideanGeometry3VectorExpression.EuclideanGeometry3CoordVector X Y Z
def geom2expr : EuclideanGeometry3VectorExpression := X⬝Y⬝Z
#check EuclideanGeometry3VectorExpression.EuclideanGeometry3CoordVector X Y Z
#check  R ⬝ geomexpr
-/

/-
def EvalEuclideanGeometry3FrameExpression : EuclideanGeometry3SpaceExpression → EuclideanGeometrySpace 3
| (EuclideanGeometry3SpaceExpression.EuclideanGeometry3Literal sp) := sp
def EvalClassicalVelocity3FrameExpression : ClassicalVelocity3SpaceExpression → ClassicalVelocitySpace 3
| (ClassicalVelocity3SpaceExpression.ClassicalVelocity3Literal sp) := sp
def EvalClassicalTimeFrameExpression {sp : ClassicalTimeSpace} : ClassicalTimeFrameExpression sp → ClassicalTimeFrame sp
| (ClassicalTimeFrameExpression.FrameLiteral fr) := fr
-/


--def DefaultEuclideanGeometry3ScalarInterp : EuclideanGeometry3ScalarInterp := λ scalar, EuclideanGeometry3ScalarDefault
--def DefaultClassicalTimeScalarInterp : ClassicalTimeScalarInterp := λ scalar, ClassicalTimeScalarDefault
--def DefaultClassicalVelocity3ScalarInterp : ClassicalVelocity3ScalarInterp := λ scalar, ClassicalVelocity3ScalarDefault

/-
def DefaultEuclideanGeometry3VectorInterp : EuclideanGeometry3VectorInterp := λ vector, EuclideanGeometry3VectorDefault geom3
def DefaultClassicalTimeVectorInterp : ClassicalTimeVectorInterp := λ vector, ClassicalTimeVectorDefault ClassicalTime
def DefaultClassicalVelocity3VectorInterp : ClassicalVelocity3VectorInterp := λ vector, ClassicalVelocity3VectorDefault vel
def DefaultEuclideanGeometry3PointInterp : EuclideanGeometry3PointInterp := λ point, EuclideanGeometry3PointDefault geom3
def DefaultClassicalTimePointInterp : ClassicalTimePointInterp := λ point, ClassicalTimePointDefault ClassicalTime
-/
--def DefaultClassicalVelocity3PointInterp : ClassicalVelocity3PointInterp := λ point, ClassicalVelocity3Point_zero

/-
def realScalarEval : RealScalarExpression → RealScalarInterp → ℝ  
| (RealScalarExpression.RealLitScalar r) i := r.val
| (RealScalarExpression.RealVarScalar v) i := (i v).val
| (RealScalarExpression.RealAddScalarScalar e1 e2) i := (realScalarEval e1 i) + (realScalarEval e2 i)
| (RealScalarExpression.RealSubScalarScalar e1 e2) i := (realScalarEval e1 i) - (realScalarEval e2 i)
| (RealScalarExpression.RealMulScalarScalar e1 e2) i := (realScalarEval e1 i) * (realScalarEval e2 i)
| (RealScalarExpression.RealNegScalar e) i := -1 * (realScalarEval e i)
| (RealScalarExpression.RealParenScalar e) i := realScalarEval e i
| (RealScalarExpression.RealDivScalarScalar e1 e2) i := RealScalarDefault.val
| (RealScalarExpression.RealInvScalar e) i := RealScalarDefault.val


def EuclideanGeometry3ScalarEval : EuclideanGeometry3ScalarExpression → EuclideanGeometry3ScalarInterp → ℝ 
| (EuclideanGeometry3ScalarExpression.GeometricLitScalar r) i := r.val
| (EuclideanGeometry3ScalarExpression.GeometricVarScalar v) i := (i v).val
| (EuclideanGeometry3ScalarExpression.GeometricAddScalarScalar e1 e2) i := (EuclideanGeometry3ScalarEval e1 i) + (EuclideanGeometry3ScalarEval e2 i)
| (EuclideanGeometry3ScalarExpression.GeometricSubScalarScalar e1 e2) i := (EuclideanGeometry3ScalarEval e1 i) - (EuclideanGeometry3ScalarEval e2 i)
| (EuclideanGeometry3ScalarExpression.GeometricMulScalarScalar e1 e2) i := (EuclideanGeometry3ScalarEval e1 i) * (EuclideanGeometry3ScalarEval e2 i)
| (EuclideanGeometry3ScalarExpression.GeometricNegScalar e) i := -1 * (EuclideanGeometry3ScalarEval e i)
| (EuclideanGeometry3ScalarExpression.GeometricParenScalar e) i := EuclideanGeometry3ScalarEval e i
| (EuclideanGeometry3ScalarExpression.GeometricDivScalarScalar e1 e2) i := EuclideanGeometry3ScalarDefault.val
| (EuclideanGeometry3ScalarExpression.GeometricInvScalar e) i := EuclideanGeometry3ScalarDefault.val
| (EuclideanGeometry3ScalarExpression.GeometricNormVector v) i := EuclideanGeometry3ScalarDefault.val


def ClassicalTimeScalarEval : ClassicalTimeScalarExpression → ClassicalTimeScalarInterp → ℝ 
| (ClassicalTimeScalarExpression.ClassicalTimeLitScalar r) i := r.val
| (ClassicalTimeScalarExpression.ClassicalTimeVarScalar v) i := (i v).val
| (ClassicalTimeScalarExpression.ClassicalTimeAddScalarScalar e1 e2) i := (ClassicalTimeScalarEval e1 i) + (ClassicalTimeScalarEval e2 i)
| (ClassicalTimeScalarExpression.ClassicalTimeSubScalarScalar e1 e2) i := (ClassicalTimeScalarEval e1 i) - (ClassicalTimeScalarEval e2 i)
| (ClassicalTimeScalarExpression.ClassicalTimeMulScalarScalar e1 e2) i := (ClassicalTimeScalarEval e1 i) * (ClassicalTimeScalarEval e2 i)
| (ClassicalTimeScalarExpression.ClassicalTimeNegScalar e) i := -1 * (ClassicalTimeScalarEval e i)
| (ClassicalTimeScalarExpression.ClassicalTimeParenScalar e) i := ClassicalTimeScalarEval e i
| (ClassicalTimeScalarExpression.ClassicalTimeDivScalarScalar e1 e2) i := ClassicalTimeScalarDefault.val
| (ClassicalTimeScalarExpression.ClassicalTimeInvScalar e) i := ClassicalTimeScalarDefault.val
| (ClassicalTimeScalarExpression.ClassicalTimeNormVector v) i := ClassicalTimeScalarDefault.val


def ClassicalVelocity3ScalarEval : ClassicalVelocity3ScalarExpression → ClassicalVelocity3ScalarInterp → ℝ 
| (ClassicalVelocity3ScalarExpression.VelocityLitScalar r) i := r.val
| (ClassicalVelocity3ScalarExpression.VelocityVarScalar v) i := (i v).val
| (ClassicalVelocity3ScalarExpression.VelocityAddScalarScalar e1 e2) i := (ClassicalVelocity3ScalarEval e1 i) + (ClassicalVelocity3ScalarEval e2 i)
| (ClassicalVelocity3ScalarExpression.VelocitySubScalarScalar e1 e2) i := (ClassicalVelocity3ScalarEval e1 i) - (ClassicalVelocity3ScalarEval e2 i)
| (ClassicalVelocity3ScalarExpression.VelocityMulScalarScalar e1 e2) i := (ClassicalVelocity3ScalarEval e1 i) * (ClassicalVelocity3ScalarEval e2 i)
| (ClassicalVelocity3ScalarExpression.VelocityNegScalar e) i := -1 * (ClassicalVelocity3ScalarEval e i)
| (ClassicalVelocity3ScalarExpression.VelocityParenScalar e) i := ClassicalVelocity3ScalarEval e i
| (ClassicalVelocity3ScalarExpression.VelocityDivScalarScalar e1 e2) i := ClassicalVelocity3ScalarDefault.val
| (ClassicalVelocity3ScalarExpression.VelocityInvScalar e) i := ClassicalVelocity3ScalarDefault.val
| (ClassicalVelocity3ScalarExpression.VelocityNormVector v) i := ClassicalVelocity3ScalarDefault.val




def EuclideanGeometry3VectorEval : EuclideanGeometry3VectorExpression → EuclideanGeometry3VectorInterp → EuclideanGeometry3Vector
| (EuclideanGeometry3VectorExpression.EuclideanGeometry3LitVector vec) i := vec
| (EuclideanGeometry3VectorExpression.EuclideanGeometry3VarVector v) i := i v
| (EuclideanGeometry3VectorExpression.EuclideanGeometry3AddVectorVector v1 v2) i := EuclideanGeometry3VectorDefault geom3
| (EuclideanGeometry3VectorExpression.EuclideanGeometry3NegVector v) i := EuclideanGeometry3VectorDefault geom3
| (EuclideanGeometry3VectorExpression.EuclideanGeometry3MulScalarVector c v) i := EuclideanGeometry3VectorDefault geom3
| (EuclideanGeometry3VectorExpression.EuclideanGeometry3MulVectorScalar v c) i := EuclideanGeometry3VectorDefault geom3
| (EuclideanGeometry3VectorExpression.EuclideanGeometry3SubPointPoint p1 p2) i := EuclideanGeometry3VectorDefault geom3
| (EuclideanGeometry3VectorExpression.EuclideanGeometry3ParenVector v) i := EuclideanGeometry3VectorDefault geom3
| (EuclideanGeometry3VectorExpression.EuclideanGeometry3CoordVector x y z) i := EuclideanGeometry3VectorDefault geom3






def ClassicalVelocity3VectorEval : ClassicalVelocity3VectorExpression → ClassicalVelocity3VectorInterp → ClassicalVelocity3Vector
| _ _ := ClassicalVelocity3VectorDefault vel

def ClassicalTimeVectorEval : ClassicalTimeVectorExpression → ClassicalTimeVectorInterp → ClassicalTimeVector
| _ _ := ClassicalTimeVectorDefault ClassicalTime

def EuclideanGeometry3PointEval : EuclideanGeometry3PointExpression → EuclideanGeometry3PointInterp → EuclideanGeometry3PointStruct
| _ _ := EuclideanGeometry3PointDefault geom3


def ClassicalTimePointEval : ClassicalTimePointExpression → ClassicalTimePointInterp → ClassicalTimePointStruct
| _ _ := ClassicalTimePointDefault ClassicalTime
-/
/-
| (RealScalarExpression.RealLitScalar r) i := r
| (RealScalarExpression.RealVarScalar v) i := i v
| (RealScalarExpression.RealAddScalarScalar e1 e2) i := realScalarEval e1 i + realScalarEval e2 i
| (RealScalarExpression.RealSubScalarScalar e1 e2) i := realScalarEval e1 i - realScalarEval e2 i
| (RealScalarExpression.RealMulScalarScalar e1 e2) i := realScalarEval e1 i * realScalarEval e2 i
| (RealScalarExpression.RealDivScalarScalar e1 e2) i := realScalarEval e1 i / realScalarEval e2 i
| (RealScalarExpression.RealNegScalar e) i := -1 * realScalarEval e i
| (RealScalarExpression.RealInvScalar e) i := 1 / realScalarEval e i
| (RealScalarExpression.RealParenScalar e) i := realScalarEval e i
-/

/-
important for static analysis!!

100 scalar variables

nontrivial : map them individually to a value that makes sense, can change at different points in  program

start of program : interp mapping 1

end of program : interp mapping n

default : map them all to 0

-/
/-
REAL PROGRAM : 100 variables

95 "UNKNOWN"
~ loose bound on "5" of them


CTRLH ℝ → ℚ 
-/





