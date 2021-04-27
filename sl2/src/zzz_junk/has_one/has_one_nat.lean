import .has_one

namespace hidden

-- Overload has_mul_ident for nat
instance has_one_nat : has_one nat := ⟨ 1, sorry, sorry ⟩
/-
Again this code would typically go in the module
that defines the nat type, as here we define an
implementation of ident_nat for this type.
-/

/-
Now anywhere else in a code base that we need a nat,
we can use typeclass inference to find the instance,
n, of the has_mul_id typeclass for the nat type and
use it to return a satisfactory answer. 
-/
def getMeANat [n : has_one nat] : nat := n.one

#eval getMeANat

end hidden