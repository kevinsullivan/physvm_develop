import ..has_mul.has_mul

namespace hidden

universe u

/-
@[class]  
structure has_one (α : Type u) extends hidden.has_mul α := 
--(mul : α → α → α)  --inherited from has_mul
(one: α)
-- preview of what's coming
(one_mul : ∀ (a : α ), mul one a = a)
(mul_one : ∀ (a : α ), mul a one = a )
--         ^^^^^^^^^^^^^^ proposition
-- proofs
-/


@[class]  
structure has_one (α : Type u) := 
--(mul : α → α → α)  --inherited from has_mul
(one: α)


end hidden