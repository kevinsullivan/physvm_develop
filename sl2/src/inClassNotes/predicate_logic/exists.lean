/-
Exists introduction. To prove ∃ (p : P), Q
-/

/-
A proof of ∃ (p : P), Q is a *dependent* pair,
⟨ p, q ⟩, where (p : P) is a "witness" to the
existential proposition, and q is a proof of 
Q. 

Very often, Q will be *about* p, e.g., that
p is an "odd prime", or a "nice person". Q 
will be the result of aplying a predicate Q'
to P. Q is short for Q' p, with Q' : Person 
→ Prop being a property of a person, such as
the property of being nice. 

∃ (p : Person), Q' p thus asserts that there 
is *some* person with property Q'. So a proof
of this proposition will be a dependent pair,
⟨ (p : P), (q : Q' p) ⟩, with Q' a predicate
on values, p, of type P.
-/

example : ∃ (n : nat), n = 0 :=
⟨ 0, eq.refl 0 ⟩ 

/-
There exists a natural number that is the square
of another natural number. 
-/
example : ∃ (n : nat), ∃ (m : nat), n = m*m :=
⟨4, ⟨2, rfl⟩ ⟩ 

example : ∃ (n : nat), ∃ (m : nat), n = m*m :=
begin
end

/-
If everyone likes Mary then someone likes Mary.
-/
axiom Person : Type
axiom Mary : Person
axiom Likes : Person → Person → Prop


example : 
(∀ (p : Person), Likes p Mary) → 
(∃ (q : Person), Likes q Mary) :=
begin
  assume h,
  refine ⟨Mary, _⟩,
  apply h Mary,
end 

/-
Exercise: ∃ elimination.
-/


/-
Practice
-/

-- Proof of transitivity of → 
example : ∀ (P Q R : Prop), (P → Q) → (Q → R) → (P → R) :=
begin
  assume P Q R pq qr p,
  apply qr (pq p),
end

example : ∀ (P Q R : Prop), (P → Q) → (Q → R) → (P → R) :=
λ P Q R pq qr p, 
  qr 
    (pq 
      p
    )

example : ∀ (P : Prop), P ∧ ¬ P → false :=
begin
 assume (P : Prop),
 assume (pnp : P ∧ ¬ P),
 cases pnp with p np,
 apply np p,
end

example : ∀ (n : nat), n = 0 ∨ n ≠ 0 :=
begin
  assume n,
  cases n,
  apply or.inl rfl,
  apply or.inr _,
  assume ns,
  cases ns,
end

example : ∀ (n : nat), n = 0 ∨ n ≠ 0 :=
λ (n : nat),
  match n with
  | nat.zero := or.inl (rfl)
  | (nat.succ n') := or.inr (λ sn, 
    match sn with
    end
  )
  end

/-
Prove, ∀ (n : nat), n = 0 ∨ n ≠ 0.

Proof. To begin, we'll assume that n
is an arbitrary natural number (forall
introduction) and in this context what
remains to be proved is n = 0 ∨ n ≠ 0.

Proof: By case analysis on the possible
forms of n.

Case 1, base case: n = 0. In this case
the disjuction is 0 = 0 ∨ ) ≠ 0 is true
because the left disjuct is trivially 
true (by reflexivity of equality).

Case 2: n = succ n'. What remains to be
proved is succ n' = 0 ∨ succ n' ≠ 0.  We
will prove this is true by proving that
the right hand side is true: succ n' ≠ 0.

Proof: This is true by Peano's axioms of
arithmetic. Zero is axomatically not equal
to any other natural number. 
-/

example : ∀ (n : nat), ∃ m, m = n + 2 :=
λ n, 
begin
  apply exists.intro (n+2), 
  apply rfl,
end


