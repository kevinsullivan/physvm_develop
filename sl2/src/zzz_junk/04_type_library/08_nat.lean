#print nat

namespace hidden

/-
The nat type represents the set
of natural numbers, and infinite
set. It explains that a natural 
number is either zero or it's one 
more than (the successor, succ, 
of) any given natural number, n'.

This is an inductive definition
in which "larger" objects of a
given type are constructed from
smaller objects of the same type.

The induction starts with the 
base case, zero, as a term of 
type nat. By application of the
second constructor, (succ zero)
is thus also a term of type nat.
And because that's the case, by
the second constructor again, 
the term (succ (succ zero)) is
of type nat, ad infinitum.

We will interpret these terms
as *unary* representations of
natural numbers, here 0, 1, 2.
-/

inductive nat : Type
| zero
| succ (n' : nat)


end hidden