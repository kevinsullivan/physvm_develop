import ...phys.src.classical_luminous_itensity

namespace lang.classicalLuminousIntensity

structure var : Type :=
mk :: (num : ℕ) 

structure spaceVar extends var

def myvar : spaceVar := ⟨⟨2⟩⟩

def p : spaceVar := ⟨⟨1⟩⟩

inductive spaceExpr
| lit (v : classicalLuminousIntensity) 
| var (v : spaceVar)
abbreviation spaceEnv := spaceVar → classicalLuminousIntensity
abbreviation spaceEval := spaceExpr → spaceEnv → classicalLuminousIntensity



structure QuantityVar extends var
inductive QuantityExpr
| lit (f : classicalLuminousIntensityQuantity)
| var (v : QuantityVar) 
abbreviation QuantityEnv := QuantityVar → classicalLuminousIntensityQuantity
abbreviation QuantityEval := QuantityExpr → QuantityEnv → classicalLuminousIntensityQuantity


def spaceVarEq : spaceVar → spaceVar → bool
| v1 v2 := v1.num=v2.num
def QuantityVarEq : QuantityVar → QuantityVar → bool
| v1 v2 := v1.num=v2.num

structure env : Type :=
(sp : spaceEnv)
(s : QuantityEnv)



noncomputable def initSp := λ v : spaceVar, classicalLuminousIntensity.build 9999
noncomputable def initQuantity := 
    λ v : QuantityVar, 
        classicalLuminousIntensityQuantity.build (initSp ⟨⟨9999⟩⟩) ⟨[1],rfl⟩
noncomputable def 
    initEnv : env := 
        ⟨initSp, initQuantity⟩

end lang.classicalLuminousIntensity