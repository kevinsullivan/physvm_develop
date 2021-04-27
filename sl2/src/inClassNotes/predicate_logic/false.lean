/-
In Lean, false is a proposition that
is false in the sense that there is
no proof of it. It's an uninhabited
type.
-/

#check false

/-
inductive false : Prop
-/

/-
There's no introduction rule for false
as there are no proofs of it at all.
-/

/-
The elimination rule for false is very
important.
-/

theorem false_elim' : ∀ (P : Prop), false → P :=    -- false elimination
λ P f, 
  match f with
  end

theorem false_imp_anything : ∀ (P : Prop), false → P :=
λ P f, false.elim f

-- Universal specialization
lemma false_imp_false : false → false := false_imp_anything false

lemma false_imp_true : false → true := false_imp_anything true

-- trick question
lemma true_imp_false : true → false := λ t, _   -- stuck 

/-
As expected from propositional logic

true → true   is true
true → false  is false
false → true  is true
false → false is true
-/




