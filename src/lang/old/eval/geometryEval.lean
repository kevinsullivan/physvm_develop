import ..imperative_DSL.environment


open lang.euclideanGeometry3

attribute [reducible]
def euclideanGeometry3Eval : lang.euclideanGeometry3.spaceExpr → environment.env → euclideanGeometry3
| (lang.euclideanGeometry3.spaceExpr.lit V) i := V
| (lang.euclideanGeometry3.spaceExpr.var v) i := i.g.sp v

attribute [reducible]
def euclideanGeometry3FrameEval : lang.euclideanGeometry3.frameExpr → environment.env → euclideanGeometry3Frame
| (lang.euclideanGeometry3.frameExpr.lit V) i := V
| (lang.euclideanGeometry3.frameExpr.var v) i := i.g.fr v

attribute [reducible]
def euclideanGeometry3TransformEval : lang.euclideanGeometry3.TransformExpr → environment.env → euclideanGeometry3Transform
| (lang.euclideanGeometry3.TransformExpr.lit V) i := V
| (lang.euclideanGeometry3.TransformExpr.var v) i := i.g.tr v


attribute [reducible]
def euclideanGeometry3ScalarEval : lang.euclideanGeometry3.ScalarExpr → environment.env → euclideanGeometry3Scalar
| (lang.euclideanGeometry3.ScalarExpr.lit V) i := V
| (lang.euclideanGeometry3.ScalarExpr.var v) i := i.g.s v


attribute [reducible]
def euclideanGeometry3AngleEval : lang.euclideanGeometry3.AngleExpr → environment.env → euclideanGeometry3Angle
| (lang.euclideanGeometry3.AngleExpr.lit V) i := V
| (lang.euclideanGeometry3.AngleExpr.var v) i := i.g.a v

attribute [reducible]
def euclideanGeometry3OrientationEval : lang.euclideanGeometry3.OrientationExpr → environment.env → euclideanGeometry3Orientation
| (lang.euclideanGeometry3.OrientationExpr.lit V) i := V
| (lang.euclideanGeometry3.OrientationExpr.var v) i := i.g.or v

attribute [reducible]
def euclideanGeometry3RotationEval : lang.euclideanGeometry3.RotationExpr → environment.env → euclideanGeometry3Rotation
| (lang.euclideanGeometry3.RotationExpr.lit V) i := V
| (lang.euclideanGeometry3.RotationExpr.var v) i := i.g.r v

attribute [reducible]
def euclideanGeometry3CoordinateVectorEval : lang.euclideanGeometry3.CoordinateVectorExpr → environment.env → euclideanGeometry3CoordinateVector
| (lang.euclideanGeometry3.CoordinateVectorExpr.lit V) i := V
| (lang.euclideanGeometry3.CoordinateVectorExpr.var v) i := i.g.vec v


attribute [reducible]
def euclideanGeometry3CoordinatePointEval : 
    lang.euclideanGeometry3.CoordinatePointExpr → environment.env → euclideanGeometry3CoordinatePoint
| (lang.euclideanGeometry3.CoordinatePointExpr.lit V) i := V
| (lang.euclideanGeometry3.CoordinatePointExpr.var v) i := i.g.pt v

