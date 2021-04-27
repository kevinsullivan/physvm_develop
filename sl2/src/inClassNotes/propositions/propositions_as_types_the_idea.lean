/-
Propositions as types: the very idea.
-/

/-
Idea #1. Use types to represent
logical propositions and values of
these types to represent "evidence" 
or "proofs" of truth. A type that
is inhabited we then judge to be
logically true, and one that is 
uninhabited we judge to be false. 
-/

/-
Idea #2. When we use values of a
type only to represent evidence
of logical truth, then it doesn't
really matter *which* value of a
type we pick as evidence. To the 
first order, we don't care which
proof of a theorem a mathematician
produces, only that there is at
least one. And indeed, any proof
will do to justify a judgment that
a proposition is true. So when we
represent propositions as types and
proofs as values, in some sense we
want every proof of a given type to
be equivalent to any other. We want
every value of a "logical" type to
be equivalent to any other. Making
this equivalence of proof terms is
one of the main purposes of the last
of Lean's type universes, which we 
now introduce: Prop. 
-/

inductive its_raining : Prop  -- not quite right
| i_see_rain_falling : its_raining
| i_hear_rain_on_roof : its_raining

inductive streets_wet : Prop
| i_see_wet_streets : streets_wet
| i_feel_wet_streets : streets_wet

open its_raining streets_wet

def proof_1'' : its_raining := i_see_rain_falling
def proof_2'' : its_raining := i_hear_rain_on_roof

lemma proof_1' : its_raining := i_see_rain_falling
lemma proof_2' : its_raining := i_hear_rain_on_roof

theorem proof_1 : its_raining := i_see_rain_falling
theorem proof_2 : its_raining := i_hear_rain_on_roof

/-
We just don't care which value of a
propositional type is used. Values
build by different constructors in 
Type n, are always NOT equal. This 
is the idea that "constructors are
injective and disjoint."
-/

/-
Prop        Sort 0
Type 0      Sort 1
Type 1      Sort 2
Type 2      Sort 3       
...         ...
-/

-- Change Type to Prop above!

/-
Just as we can represent propositions
as types, we can represent *predicates*
as type families indexed by arguments, 
i.e., as "propositions with parameters."
-/

inductive day : Type 
| su | mo | tu | we | th | fr | sa 

open day

/-
A type family indexed by day representing
the predicate ⟨ is_always_rainy d ⟩, where
d is a parameter of type day. Providing a
value for d yields a specific proposition
in the family of propositions we've defined, 
namely one claims that a specific day, d, is
always rainy. 
-/

inductive is_always_rainy : day → Sort 0
| mo_rainy : ∀ (d :day), (d = mo) → is_always_rainy d

open is_always_rainy

#check is_always_rainy
#check is_always_rainy su
#check is_always_rainy mo
#check is_always_rainy tu



lemma bad_tuesdays : is_always_rainy tu := mo_rainy _ _ -- stuck
lemma bad_fridays : is_always_rainy fr := mo_rainy _ _    -- stuck
lemma bad_mondays : is_always_rainy mo := mo_rainy mo (eq.refl mo)

