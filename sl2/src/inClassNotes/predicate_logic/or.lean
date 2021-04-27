/-
If P and Q are propositions, then so in P ∨ Q.
We want to judge P ∨ Q to be true if at least
one of them is true. In other words, to judge
P ∨ Q to be true, we need either to be able to
judge P to be true or Q to be true (and if both
are true, that's fine, too).
-/

#check or

/-
inductive or (a b : Prop) : Prop
| inl (h : a) : or
| inr (h : b) : or
-/

/-
It's a polymorphic "either" type (in Prop)!
-/


axioms (P Q : Prop) (p : P)

lemma porq' : P ∨ Q := or.inl p

lemma porq'' : P ∨ Q := 
begin
apply or.inl _,
exact p,
end

axiom q : Q

lemma porq''' : P ∨ Q := or.inr q

/-
def or.intro_left {a : Prop} (b : Prop) (ha : a) : or a b :=
or.inl ha

def or.intro_right (a : Prop) {b : Prop} (hb : b) : or a b :=
or.inr hb
-/


/-
Suppose it's raining or the sprinkler is running.
Futhermore, suppose that if it's raining the grass
is wet, and if the sprinkler is running then the
grass is wet? What can you conclude? 
-/

/-
You *used* the fact that at least one of the cases
held, combined with the fact that in *either* case,
the grass is wet, to deduce that the grass is wet.
-/

axioms (R : Prop) (porq : P ∨ Q) (pr : P → R) (qr : Q → R)

theorem RisTrue : R := or.elim porq pr qr

theorem RisTrue' : R := 
begin
apply or.elim porq, 
exact pr,
exact qr,
end


/- Or -/

/-
inductive or (a b : Prop) : Prop
| inl (h : a) : or
| inr (h : b) : or
-/

-- commutes forward, proof term
example : P ∨ Q → Q ∨ P :=
λ h, 
  (match h with 
  | or.inl p := or.inr p
  | or.inr q := or.inl q
  end)

-- commutes forward, tactic script
example : P ∨ Q → Q ∨ P :=
begin
  assume porq,
  cases porq with p q,
  exact or.inr p,
  exact or.inl q,
end

/-
or is associative, full proof
-/
example : P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R := 
begin
  apply iff.intro _ _,
  
  -- Forwards ->
  assume pqr,
  cases pqr with p qr,
  apply or.inl _,
  exact or.inl p,
  cases qr with q r,
  apply or.inl,
  exact or.inr q,
  exact or.inr r,

  -- Backwards <-
  assume pqr, 
  cases pqr,
  _
end