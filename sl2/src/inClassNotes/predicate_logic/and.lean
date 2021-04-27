/-
The connective, ∧, in predicate as in
propositional logic builds a proposition
that asserts that each of two propositions
is true. Given propositions P, Q, P ∧ Q 
is also a proposition, and we judge it to
be true iff we judge P to be true and we
judge Q to be true. We judge P and Q to
be true iff we have evidence that they
are true, in the form of proofs. Our rule
for constructing evidence for P ∧ Q thus
demands evidence for P and evidence for
Q and yields evidence for P ∧ Q. 
-/

#check and

/-
structure and (a b : Prop) : Prop :=
intro :: (left : a) (right : b)
-/

-- A polymorphic product type (in Prop)!

axioms (P Q : Prop) (p : P) (q : Q)

example : P := p
example : Q := q
example : P ∧ Q := and.intro p q
lemma paq : P ∧ Q := ⟨ p, q ⟩ 

#check paq
#reduce paq 

#check and.elim_left

/-
def and.elim_left {a b : Prop} (h : and a b) : a := h.1
def and.elim_right {a b : Prop} (h : and a b) : b := h.2
-/

#reduce and.elim_left paq
#reduce and.elim_right paq

example : 0 = 0 ∧ 1 = 0 :=
and.intro (eq.refl 0) (eq.refl _)   -- stuck


lemma zzoo : 0 = 0 ∧ 1 = 1 :=
and.intro rfl rfl 

#reduce zzoo.right

/-
Proof that and commutes and is
associative (you can regroup at
will, by associativity). 
-/

example : P ∧ Q → Q ∧ P :=
λ (h : P ∧ Q), and.intro h.right h.left

/-
And is commutative and associative. 
Prove it.
-/
axiom R : Prop

lemma and_assoc_forward : (P ∧ Q) ∧ R -> P ∧ (Q ∧ R) :=
λ h, 
  (and.intro 
    h.left.left 
   (and.intro h.left.right h.right)
  )

/-
Full proof. and commutes
-/
example : P ∧ Q ↔ Q ∧ P :=

-- proof is pair: forward/backward proofs
iff.intro 
  -- proof forward
  (λ h, ⟨ h.right, h.left ⟩ )
  -- proof backwards
  (λ h, ⟨ h.right, h.left ⟩)

/-
Full proof, modulo reverse direction,
that and is associative.
-/
example : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) :=
iff.intro 
  (and_assoc_forward)
  (_)
  