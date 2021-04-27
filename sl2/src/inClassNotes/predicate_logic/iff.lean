/-
Given propositions P and Q, to prove P ↔ Q 
requires a proof of P → Q and a proof of 
Q → P. The introduction rule is iff.intro :
(P → Q) → (Q → P) → P ↔ Q.
-/

#check iff
#check @iff.intro

/-
structure iff (a b : Prop) : Prop :=
intro :: (mp : a → b) (mpr : b → a)
-/

/-
It's a special case of and. The elimination
rules are analogous, too. Remember reading
the next types that → is right associative.
-/

#check @iff.elim_left
#check @iff.elim_right


/-
Example. 1 = 1 ↔ 0 = 0.
-/

example : 1 = 1 ↔ 0 = 0 :=
iff.intro 
  (λ _, rfl)   -- ⊢ 1 = 1 → 0 = 0
  (λ _, rfl)   -- ⊢ 0 = 0 → 1 = 1

/-
And so for the eliminators.
-/

#check @iff.elim_left
#check @iff.elim_right

/- 
Show: ∀ (P Q : Prop), (P ↔ Q) → Q → P.
-/

example : ∀ (P Q : Prop), (P ↔ Q) → Q → P := 
λ P Q h q,    
  -- use what you have to make what you need
  _


/-
General requirement to prove P ↔ Q is to 
give proofs of P → Q and Q → P to ↔-intro. 
That is, apply ↔-intro to a proof of P → Q
and a proof of Q → P. Thus:

iff.intro : (P → Q) → (Q → P) → (P ↔ Q)
iff.elim_left : (P ↔ Q) → (P → Q)
iff.elim_right : (P ↔ Q) → (Q → P)
-/

-- Exercise: Try it to test yourself.

