/-
Provides definitions so that we can have additive group actions.
-/

import algebra.group.basic

universes u v
variables {α : Type u} {β : Type v}

/-- Typeclass for types with transformation functions.
For our purposes, those transformations are translations by a vector. -/
class has_trans (α : Type u) (γ : Type v) := (sadd : α → γ → γ)

infixr ` ⊹ `:73 := has_trans.sadd -- notation for group addition

/-- Typeclass for additive actions by additive groups. -/
class add_action (α : Type u) (β : Type v) [add_group α] extends has_trans α β :=
(zero_sadd : ∀ b : β, (0 : α) ⊹ b = b)
(add_sadd : ∀ (x y : α) (b : β), (x + y) ⊹ b = x ⊹ y ⊹ b)
