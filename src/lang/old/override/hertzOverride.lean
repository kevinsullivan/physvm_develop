import ..imperative_DSL.environment
import ..eval.hertzEval

open lang.classicalHertz

def assignHertzSpace : environment.env → lang.classicalHertz.spaceVar → lang.classicalHertz.spaceExpr → environment.env
| i v e :=
  {
    h:={sp := (λ r,     
                if (spaceVarEq v r) 
                then (classicalHertzEval e i) 
                else (i.h.sp r)), ..i.h},
    ..i
  }
  

def assignHertzQuantity : environment.env → 
  lang.classicalHertz.QuantityVar → 
  lang.classicalHertz.QuantityExpr → environment.env 
| i v e := 
  {
    h:={s := (λ r,     
                if (QuantityVarEq v r) 
                then (classicalHertzQuantityEval e i) 
                else (i.h.s r)), ..i.h},
    ..i
  }