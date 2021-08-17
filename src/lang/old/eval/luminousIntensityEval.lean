import ..imperative_DSL.environment


open lang.classicalLuminousIntensity

attribute [reducible]
def classicalLuminousIntensityEval : lang.classicalLuminousIntensity.spaceExpr → environment.env → classicalLuminousIntensity
| (lang.classicalLuminousIntensity.spaceExpr.lit V) i := V
| (lang.classicalLuminousIntensity.spaceExpr.var v) i := i.li.sp v

attribute [reducible]
def classicalLuminousIntensityQuantityEval : lang.classicalLuminousIntensity.QuantityExpr → environment.env → classicalLuminousIntensityQuantity
| (lang.classicalLuminousIntensity.QuantityExpr.lit V) i := V
| (lang.classicalLuminousIntensity.QuantityExpr.var v) i := i.li.s v
