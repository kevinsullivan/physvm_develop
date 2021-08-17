import ..imperative_DSL.environment


open lang.classicalHertz

attribute [reducible]
def classicalHertzEval : lang.classicalHertz.spaceExpr → environment.env → classicalHertz
| (lang.classicalHertz.spaceExpr.lit V) i := V
| (lang.classicalHertz.spaceExpr.var v) i := i.h.sp v

attribute [reducible]
def classicalHertzQuantityEval : lang.classicalHertz.QuantityExpr → environment.env → classicalHertzQuantity
| (lang.classicalHertz.QuantityExpr.lit V) i := V
| (lang.classicalHertz.QuantityExpr.var v) i := i.h.s v
