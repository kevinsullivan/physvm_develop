/-
In Lean, true is a proposition that
is always true, in the sense that
there is a proof of it that doesn't
depend on anything else being true.
-/

#check true

/-
inductive true : Prop
| intro : true
-/


/-
Introduction rule for true
-/
lemma true_is_true : true := true.intro


/-
A function from true to true
-/
lemma true_to_true' : true → true := 
λ (t : true), t


/-
A proof that true → true
-/
lemma true_to_true : true → true := 
λ t, t
