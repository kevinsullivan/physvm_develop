/-
If P and Q are propositions, then P → Q
is a proposition, as well. We just such
an implication to be true if whenever P
is true Q must be true as well. To prove
P → Q, we thus *assume* that P is true
(and in constructive logic this means we
assume we have a proof of it, p : P), and
in the context of this assumption, we show
that Q must be true, in the sense that we
can produce evidence (q : Q) that this is
the case.

This is a long way of saying that to prove
P → Q, we assume we have a proof of P and
in this context we must produce a proof of
Q. In the constructive logic of Lean, this
means we prove P → Q by showing that there
is a function of type P to Q! Of course a
function of this type is really a function
of type ∀ (p : P), Q, which is notation for
Π (p : P), Q which is just a non-dependent
function type, P → Q. It all makes sense! 
-/

lemma and_commutes' : ∀ {P Q : Prop}, P ∧ Q → Q ∧ P :=
λ P Q, λ h, and.intro (h.right) (h.left) 

/-
This is the introduction rule for →. Assume 
you have a proof of the antcedent (P ∧ Q in 
this case) and show that in that context
there is a proof of the conclusion (Q ∧ P).
-/

/-
Elimination
-/
axioms (Person : Type) (fromCville : Person → Prop)
axioms (Kevin Liu : Person) (kfc : fromCville Kevin) (lfc : fromCville Liu)

-- let's construct a proof of fromCville Kevin ∧ fromCville Liu (P ∧ Q)
theorem bfc : fromCville Kevin ∧ fromCville Liu := and.intro kfc lfc

#check bfc
#reduce bfc

-- now we can *apply* and_commutes' to derive a proof of (Q ∧ P)

#check and_commutes' bfc
#reduce and_commutes' bfc