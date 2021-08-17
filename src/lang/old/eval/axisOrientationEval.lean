import ..imperative_DSL.environment


open lang.axisOrientation

def axisOrientationEval : lang.axisOrientation.orientationExpr → environment.env → orientation.AxisOrientation 3
| (lang.axisOrientation.orientationExpr.lit V) i := V
| (lang.axisOrientation.orientationExpr.var v) i := i.ax.or v
