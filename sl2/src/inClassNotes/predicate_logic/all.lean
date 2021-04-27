/-
To show that something (such as n = n)
is true for *all* values of some type
(such as nat), assume that you have an
*arbitrary* value of that type and in
that context show that that something
is true for that arbitrary n. Because
it's true for an n selected arbitrarily
it must be true for every n. (Think 
about that.) This is the introduction
rule for ∀. In Lean, to prove a ∀ we
define a function: one that *assumes*
it's given an arbitrary argument of a
given type and that, in that context,
produces a value of a desired type. 
So you already know how to prove a ∀
proposition in Lean: write a function. 
-/

#check ∀ (n : nat), n = n

lemma all1 : ∀ (n : nat), n = n := λ n, (eq.refl n)       

lemma all2 (n : nat) : n = n := rfl

#check ∀ (n : nat), n = n 

-- Introduction rule for forall 

/-
Now *given* a proof of a forall, you
*use* it by *applying* it to get a 
proof for any particular instance of
a universally quantified proposition.
Suppse you know that ∀ n, n = n and
you need a proof of 5 = 5. You can
just *apply* the "proof" to 5 to get
what you need. This is the elimination
rule for ∀. 
-/

example : 5 = 5 := all1 5

#check all1 5

axioms  (Person : Type) 
        (Friendly : Person → Prop) 
        (allFriendly : ∀ (p : Person), Friendly p)
        (John : Person)

example : Friendly John := allFriendly John

/-
Proofs are just "programs" -- functions, data structures
-/




