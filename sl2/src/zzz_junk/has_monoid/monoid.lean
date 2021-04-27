import ..semigroup.semigroup
import ..has_mul.has_mul
import ..has_one.has_one


/-
A monoid is a semigroup 
with an element 1 
such that 1 * a = a * 1 = a.
-/

namespace hidden

universe u

@[class]
structure has_monoid (α : Type u) extends (hidden.semigroup α), (hidden.has_one α)  : Type u 
-- mul          -- from semigroup extends has_mul (not accessible?)
-- mul_assoc    -- from semigroup (uses mul)
-- one          -- from this structures extending from has_one


instance has_monoid_bool [semigroup bool] [has_one bool] : hidden.has_monoid bool :=
⟨ ⟩ 

instance has_monoid_nat [semigroup nat] [has_one nat] : has_monoid nat :=
⟨ ⟩ 

end hidden