import ..imperative_DSL.environment


open lang.measurementSystem

def measurementSystemEval : lang.measurementSystem.measureExpr → environment.env → measurementSystem.MeasurementSystem
| (lang.measurementSystem.measureExpr.lit V) i := V
| (lang.measurementSystem.measureExpr.var v) i := i.ms.ms v
