import ..has_mul.has_mul 
universe u

namespace hidden
/-
A semigroup is a set α (given by a type) with an associative 
multiplication operator, mul. Many sets, α, can be treated as
semigroups. A set of any kind of objects is a semigroup as long
as it has an associative binary multiplication operator, mul. 
-/

@[class]
structure semigroup (α : Type u) extends hidden.has_mul α : Type u :=
(mul_assoc : ∀ (a b c_1 : α), mul (mul a b) c_1 = mul a (mul b c_1))

#check semigroup

end hidden