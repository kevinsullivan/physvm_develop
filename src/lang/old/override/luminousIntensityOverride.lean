import ..imperative_DSL.environment
import ..eval.luminousIntensityEval

open lang.classicalLuminousIntensity

def assignLuminousIntensitySpace : environment.env → lang.classicalLuminousIntensity.spaceVar → lang.classicalLuminousIntensity.spaceExpr → environment.env
| i v e :=
  {
    li:={sp := (λ r,     
                if (spaceVarEq v r) 
                then (classicalLuminousIntensityEval e i) 
                else (i.li.sp r)), ..i.li},
    ..i
  }
  

def assignLuminousIntensityQuantity : environment.env → 
  lang.classicalLuminousIntensity.QuantityVar → 
  lang.classicalLuminousIntensity.QuantityExpr → environment.env 
| i v e := 
  {
    li:={s := (λ r,     
                if (QuantityVarEq v r) 
                then (classicalLuminousIntensityQuantityEval e i) 
                else (i.li.s r)), ..i.li},
    ..i
  }