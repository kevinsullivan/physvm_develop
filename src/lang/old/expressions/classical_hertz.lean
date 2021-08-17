import ...phys.src.classical_hertz

namespace lang.classicalHertz

structure var : Type :=
mk :: (num : ℕ) 

structure spaceVar extends var

def myvar : spaceVar := ⟨⟨2⟩⟩

def p : spaceVar := ⟨⟨1⟩⟩

inductive spaceExpr
| lit (v : classicalHertz) 
| var (v : spaceVar)
abbreviation spaceEnv := spaceVar → classicalHertz
abbreviation spaceEval := spaceExpr → spaceEnv → classicalHertz



structure QuantityVar extends var
inductive QuantityExpr
| lit (f : classicalHertzQuantity)
| var (v : QuantityVar) 
abbreviation QuantityEnv := QuantityVar → classicalHertzQuantity
abbreviation QuantityEval := QuantityExpr → QuantityEnv → classicalHertzQuantity


def spaceVarEq : spaceVar → spaceVar → bool
| v1 v2 := v1.num=v2.num
def QuantityVarEq : QuantityVar → QuantityVar → bool
| v1 v2 := v1.num=v2.num

structure env : Type :=
(sp : spaceEnv)
(s : QuantityEnv)



noncomputable def initSp := λ v : spaceVar, classicalHertz.build 9999
noncomputable def initQuantity := 
    λ v : QuantityVar, 
        classicalHertzQuantity.build (initSp ⟨⟨9999⟩⟩) ⟨[1],rfl⟩
noncomputable def 
    initEnv : env := 
        ⟨initSp, initQuantity⟩

end lang.classicalHertz