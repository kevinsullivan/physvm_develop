import ..imperative_DSL.environment


open lang.classicalTime

attribute [reducible]
def classicalTimeEval : lang.classicalTime.spaceExpr → environment.env → classicalTime
| (lang.classicalTime.spaceExpr.lit V) i := V
| (lang.classicalTime.spaceExpr.var v) i := i.t.sp v

attribute [reducible]
def classicalTimeFrameEval : lang.classicalTime.frameExpr → environment.env → classicalTimeFrame
| (lang.classicalTime.frameExpr.lit V) i := V
| (lang.classicalTime.frameExpr.var v) i := i.t.fr v

attribute [reducible]
def classicalTimeTransformEval : lang.classicalTime.transformExpr → environment.env → classicalTimeTransform
| (lang.classicalTime.transformExpr.lit V) i := V
| (lang.classicalTime.transformExpr.var v) i := i.t.tr v

attribute [reducible]
def classicalTimeScalarEval : lang.classicalTime.ScalarExpr → environment.env → classicalTimeScalar
| (lang.classicalTime.ScalarExpr.lit V) i := V
| (lang.classicalTime.ScalarExpr.var v) i := i.t.s v

attribute [reducible]
def classicalTimeCoordinateVectorEval : lang.classicalTime.CoordinateVectorExpr → environment.env → classicalTimeCoordinateVector
| (lang.classicalTime.CoordinateVectorExpr.lit V) i := V
| (lang.classicalTime.CoordinateVectorExpr.var v) i := i.t.vec v


attribute [reducible]
def classicalTimeCoordinatePointEval : 
    lang.classicalTime.CoordinatePointExpr → environment.env → classicalTimeCoordinatePoint
| (lang.classicalTime.CoordinatePointExpr.lit V) i := V
| (lang.classicalTime.CoordinatePointExpr.var v) i := i.t.pt v

