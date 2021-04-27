import ..has_mul.has_mul
import ..has_one.has_one

--- NOT TOO MUCH TO LOOK AT HERE RIGHT NOW SORRY

#check [has_mul nat]
#check [has_mul bool]

#check has_mul
#check has_mul nat
#check has_mul bool

instance has_mul_bool : has_mul bool := ⟨ band ⟩ 
instance ident_nat : has_mul nat := ⟨ nat.mul ⟩

def getMeANat [n : has_one nat] : nat := n.one

def gotAFunc [b : has_mul bool] := b.mul

#eval gotAFunc ff ff
#eval gotAFunc ff tt
#eval gotAFunc tt ff
#eval gotAFunc tt tt
-- Yep, that's band


