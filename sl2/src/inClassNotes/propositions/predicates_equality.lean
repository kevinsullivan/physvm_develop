
import inClassNotes.propositions.propositions_as_types_the_idea

/-
It's now an easy jump to using type
families indexed by two types to represent
predicates with two arguments. For example,
here's an equality predicate, representing
an equality relation, on terms of type day.
-/

open day

inductive eq_day : day → day → Prop
| eq_day_mo : eq_day mo mo
| eq_day_tu : eq_day tu tu
| eq_day_we : eq_day we we
| eq_day_th : eq_day th th
| eq_day_fr : eq_day fr fr
| eq_day_sa : eq_day sa sa
| eq_day_su : eq_day su su 

/-
eq_day = { (mo,mo), (tu,tu), ..., (su,su) }
-/



open eq_day

#check eq_day mo mo   -- inhabited thus true
#check eq_day mo tu   -- not inhabited, not true
#check eq_day fr sa   -- not inhabited, not true

lemma mos_equal : eq_day mo mo := eq_day_mo
lemma mo_tu_equal : eq_day mo tu := _ -- stuck

/-
We use predicates specify sets and relations.
Unary predicates specify sets. Binary and n-ary
predicates more generally specify relations. 

For example, always_rains_on : day → Prop
*with its particular proof constructors*
represents the set { mo }, as mo is the only
proposition in the family of propositions
for which there's a proof, i.e., that is
inhabited.

Similarly, our eq_day : day → day → Prop
type family / binary predicate specifies 
the 7-element binary relation (a set of
pairs), { (mo,mo), ..., (su,su)}, in the
sense these are all of and the only values
for which eq_day yields a proposition for
which there's a proof.
-/

/-
We can even use our home-grown equality
predicate (a binary relation) on days to
re-write our (always_rains_on d) predicate
using eq_day so that we can finish our
proof above.
-/

inductive always_rains_on' : day → Prop
| mo_rainy' : ∀ (d : day), (eq_day d mo) → always_rains_on' d

open always_rains_on'

lemma bad_tuesdays' : always_rains_on' tu := mo_rainy' tu _  -- stuck
lemma bad_fridays' : always_rains_on' fr := mo_rainy' fr _  -- stuck
lemma bad_mondays' : always_rains_on' mo := mo_rainy' mo eq_day_mo

/-
As an aside you can of course use tactic mode.
-/

lemma bad_mondays'' : always_rains_on' mo := /- term -/
begin
apply mo_rainy' _ _,
exact eq_day_mo,
end

/-
We're now completely set up to look at
a first crucial application of these
ideas: the definition of an equality
predicate in Lean. We just saw how we
can represent an equality relation on
days as a two-place predicate. 

We generalize our approach by defining
a polymorphic type family, eq. The eq 
type family takes on type parameter, α, 
and two *values* of that type, a1 and 
a2, (just as our eq_day predicate takes
two values of type day). The resulting 
proposition is (eq a b), for which Lean
gives us infix syntactic sugar, a = b.  
The type parameter is implicit. 

That defines our family of propositions. 
They include propositions such as follow.
-/


#check eq 1 1           -- a1=1
#check eq 0 1           -- 0 = 1
#check eq tt tt         -- tt = tt
#check eq tt ff         -- tt = ff
#check eq "hi" "there"  -- "hi" = "there"
#check eq mo tu         -- mo = tu

/-
The following terms are not propositions
in Lean, for they do not even type check.
-/

#check eq 1 tt
#check eq "hi" 2
#check eq tt "Lean!"


/-
The final trick is that there is just
one constructor for eq, called "refl"
(generally written eq.refl) that takes  
*one* argument, a : α, and constructs
a value of type (eq a a), aka a=a, which
we take to be a proof of equality. The 
upshot is that you can generate a proof that
any value of any type is equal to itself
and there is no way to create a proof of
any other equality. 
-/

#check @eq

/-
Here's Lean's exact definition of the
eq relation as a type family with some
members having proofs of equalty, and
other members not. The real key is to
define the constructors/axioms so that
you get exacty the relation you want!
-/

namespace eql

universe u

inductive eq {α : Sort u} (a : α) : α → Prop
| refl [] : eq a  -- skip notation for now

-- You can see exactly what's going on here
#check @eq
#check eq 1 1
#check 1 = 1    -- same thing
#check @eq.refl
#check eq.refl 1

end eql

example : 1 = 1 := eq.refl 1
example : 1 = 2 := _

/-
Moreover, Lean reduces arguments to calls
so you can use eq.refl to construct proofs
of propositions such as 1 + 1 = 2.
-/
example : 1 + 1 = 2 := eq.refl 2
example : "Hello, " ++ "Lean!" = "Hello, Lean!" := eq.refl "Hello, Lean!"

/-
By the way, "example", is like def, lemma
or theorem, but you don't bind a name to
a term. It's useful for show that a type
is inhabited by giving an example of a
value of that type. It's particularly 
useful when you don't care which value
of a type is produced, since you're not
go to do anything else with it anyway,
given that it's unnamed.
-/

/-
A note on convenient shortcuts. The rfl
function uses inference pretty heavily.
-/

example : 1 + 1 = 4 - 2 := rfl

/-
Here's the definition of rfl from Lean's library.

def rfl {α : Sort u} {a : α} : a = a := eq.refl a

Lean has to be able to infer both the (α : Type) 
and (a : α) value for this definition to work. 
-/

/-
We've thus specified the binary relation, equality,
the equality predicate, on terms of any type. What
are its properties and related functions?
-/

/- 
Properties of equality
-- reflexive
-- symmetric
-- transitive
An equivalence relation
-/

#check eq.refl
#check eq.symm
#check eq.trans
#check @eq.rec




inductive ev : ℕ → Prop
| ev_0 : ev 0
| ev_ss : ∀ (n : ℕ), ev n → ev (n+2) 

open ev

lemma zero_even : ev 0 := ev_0
lemma two_even : ev 2 := ev_ss 0 ev_0
lemma four_even : ev 4 := ev_ss 2 two_even

lemma four_even' : ev 4 := 
  ev_ss   -- emphasizes recursive structure of proof term
    2 
    (ev_ss
      0
      ev_0 
    )

lemma five_hundred_even : ev 500 :=
begin
  repeat { apply ev_ss },
  _
end