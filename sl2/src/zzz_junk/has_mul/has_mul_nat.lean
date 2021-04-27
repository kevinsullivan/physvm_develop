import .has_mul


-- Overload has_mul_ident for nat
instance ident_nat : hidden.has_mul nat := ⟨ nat.mul ⟩
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
def natMul [n : hidden.has_mul nat] := n.mul
/-
To use a typeclass, use it an an implement value
parameter in a function definition. Than you can
access all fields of the instances structure to get
the associated data (here a binary function).
-/

-- smoke test
#eval natMul 2 3