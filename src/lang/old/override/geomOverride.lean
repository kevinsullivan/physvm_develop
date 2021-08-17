import ..imperative_DSL.environment
import ..eval.geometryEval

open lang.euclideanGeometry3

def assignGeometry3Space : environment.env → lang.euclideanGeometry3.spaceVar → lang.euclideanGeometry3.spaceExpr → environment.env
| i v e :=
  {
    g:={sp := (λ r,     
                if (spaceVarEq v r) 
                then (euclideanGeometry3Eval e i) 
                else (i.g.sp r)), ..i.g},
    ..i
  }
def assignGeometry3Frame : environment.env → lang.euclideanGeometry3.frameVar → lang.euclideanGeometry3.frameExpr → environment.env
| i v e := 
  {
    g:={fr := (λ r,     
                if (frameVarEq v r) 
                then (euclideanGeometry3FrameEval e i) 
                else (i.g.fr r)), ..i.g},
    ..i
  }

def assignGeometry3Transform : environment.env → lang.euclideanGeometry3.TransformVar → lang.euclideanGeometry3.TransformExpr → environment.env
| i v e := 
  {
    g:={tr := (λ r,     
                if (transformVarEq v r) 
                then (euclideanGeometry3TransformEval e i) 
                else (i.g.tr r)), ..i.g},
    ..i
  }

def assignGeometry3Vector : environment.env → lang.euclideanGeometry3.CoordinateVectorVar → lang.euclideanGeometry3.CoordinateVectorExpr → environment.env 
| i v e := 
  {
    g:={vec := (λ r,     
                if (vectorVarEq v r) 
                then (euclideanGeometry3CoordinateVectorEval e i) 
                else (i.g.vec r)), ..i.g},
    ..i
  }

def assignGeometry3Point : environment.env → lang.euclideanGeometry3.CoordinatePointVar → lang.euclideanGeometry3.CoordinatePointExpr → environment.env 
| i v e := 
  {
    g:={pt := (λ r,     
                if (pointVarEq v r) 
                then (euclideanGeometry3CoordinatePointEval e i) 
                else (i.g.pt r)), ..i.g},
    ..i
  }

def assignGeometry3Scalar : environment.env → 
  lang.euclideanGeometry3.ScalarVar → 
  lang.euclideanGeometry3.ScalarExpr → environment.env 
| i v e := 
  {
    g:={s := (λ r,     
                if (scalarVarEq v r) 
                then (euclideanGeometry3ScalarEval e i) 
                else (i.g.s r)), ..i.g},
    ..i
  }
                

def assignGeometry3Angle : environment.env → 
  lang.euclideanGeometry3.AngleVar → 
  lang.euclideanGeometry3.AngleExpr → environment.env 
| i v e := 
  {
    g:={a := (λ r,     
                if (angleVarEq v r) 
                then (euclideanGeometry3AngleEval e i) 
                else (i.g.a r)), ..i.g},
    ..i
  }
                

def assignGeometry3Orientation : environment.env → 
  lang.euclideanGeometry3.OrientationVar → 
  lang.euclideanGeometry3.OrientationExpr → environment.env 
| i v e := 
  {
    g:={or := (λ r,     
                if (orientationVarEq v r) 
                then (euclideanGeometry3OrientationEval e i) 
                else (i.g.or r)), ..i.g},
    ..i
  }
                

def assignGeometry3Rotation : environment.env → 
  lang.euclideanGeometry3.RotationVar → 
  lang.euclideanGeometry3.RotationExpr → environment.env 
| i v e := 
  {
    g:={r := (λ r,     
                if (rotationVarEq v r) 
                then (euclideanGeometry3RotationEval e i) 
                else (i.g.r r)), ..i.g},
    ..i
  }