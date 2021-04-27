/-
If P is a proposition, then so is ¬P.
We judge ¬P to be true when P is false:
when there is no proof of it at all. 
-/

#check not

/-
def not (a : Prop) := a → false
prefix `¬` := not
-/

lemma not_false' : ¬ false := λ f, f

/-
For any proposition, P, to prove ¬P,
assume that P is true and show that
that leads to a contradiction (in the
form of a proof of false). This is 
called "proof by negation." Remember:
¬P means P → false.
-/


-- neg elimination is not constructively valid

theorem neg_elim : ∀ (P : Prop), ¬(¬P) → P := 
λ P h, _  -- have proof of this "(P → false) → false", how to get to a proof of P?

-- not constructively valid 
-- law excluded middle 


/-
  P
¬ P → false
¬ (¬ P) → P   -- negation elimination
              -- aka double negation elimination
-/


/-
¬ P means (is defined as) P → false
-/

#check false 

axiom P : Prop
axiom func : P → false 
/-
This proves ¬P!
This is a definition: ¬P means P → false
-/

#check not 

#check string.length
#check (string.length "hello")

-- impossibility elimination
example : ¬ 1 = 0 :=
λ h, 
  match h with
  -- secret sauce: there are no cases
  end

example : ¬ 1 = 0 :=  -- 1=0 → false
begin
  assume h,           -- assume 1=0
                      -- show false in all cases
                      -- but there are no cases
                      -- so that is all of them
  cases h,
end 

/-
Contradictions are impossible.
-/
lemma no_contra : ¬ (P ∧ ¬ P) :=
λ h, 
  (h.right h.left)

/-
Nonsense implies nonsense.
-/
example : 1 = 0 → 2 = 3 := 
begin
  assume h,
  cases h,
end 
