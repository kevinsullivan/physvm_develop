namespace hidden

/-
Inductive, aka algebraic, data types 
  - sum types
  - product types and case analysis
  - parametrically polymorphic
  - sum of product types and destructuring
-/

/-
SUM TYPES

A value of such a type is "one of these OR
one of those OR one of something else." SUM
means OR in this sense.
-/

inductive romanNumeral : Type
| I     : romanNumeral
| II    : romanNumeral
| III   : romanNumeral
| IV    : romanNumeral
| V     : romanNumeral


-- The empty data type
inductive empty : Type  -- Look Ma, no terms ("uninhabited")

def x : empty := _

def funny : empty → empty :=
λ (e : empty), e
-- The unit data type
inductive unit : Type   -- A type with one value (void)
| star : unit

-- The bool data type
inductive bool : Type   -- Two values
| tt : bool
| ff                    -- leave type to be inferred

-- An inductive type with seven values
inductive day : Type
| sun
| mon
| tue
| wed
| thu
| fri
| sat

open day

/-
CASE ANALYSIS 

We generally define functions that consume
values of sum types by case analysis. To know
what to return, we need to know what form of
value we got as an argument. 
-/

def next_day : day → day
| sun := mon
| mon := tue
| tue := wed
| wed := thu
| thu := fri
| fri := sat
| sat := sun


/-
The left side of a case is usually called
a pattern. Argument values are matched to
patterns in the order in which patterns are 
using a "unification" algorithm (more on that
later). Function evaluation finds the first
pattern that matches and return the result
obtained by evaluating the expression on the
right hand side of that pattern-matching
rule.
-/

#reduce next_day sun
#reduce next_day sat

/-
The _ character can be used to match any value.
All functions in Lean must be total. We often use
_ to cover all other cases no covered explicitly 
so far.
-/
def isWeekday : day → bool
| sat := bool.ff
| sun := bool.ff
| _ :=   bool.tt

/-
PRODUCT TYPES (records, structures)
-/

/-
A product type has one constructor
that takes and bundles up values of 
zero or more other types into records, 
or structures. 

In a value of a product type there a
value for the first field of an object
AND a value for the secon AND a value 
for the third, etc. PRODUCT in this
sense means AND.
-/

/-
Note: The empty type can be viewed as
also a product type with zero fields.
-/

/-
We now define a product type with 
one field. 

To understand such type definitions
you need to understand that  a
constructor, C, is like a function, 
with zero or more arguments, the only 
thing it does is to package up its
arguments into a term, (C a₀ ... aₙ). 

A value of our box type can thus be 
visualized as a box (term) with a
single value, the argument to box.mk, 
inside. 

As usual there are several syntactic
variants for defining inductive types.
-/

inductive box_nat' : Type
| mk (val : ℕ) -- : box_nat'

inductive box_nat'' : Type
| mk : ℕ → box_nat''

structure box_nat''' : Type :=   
mk :: (val : ℕ)

structure box_nat :=  -- readable
(val : ℕ) 

-- Let's create such a value
def aBox := box_nat.mk 3 

-- What does the resulting term look like?
#reduce aBox


/- 
Given a box, we "destructure" it using 
"pattern matching" to get at the values
that were used in its construction: in
this case to access the ℕ inside a box.

Here we see a more interesting form of
unification. The key ideas are (1) the
algorithm determines whether a pattern
matches, (2) it binds names to parts of
the object being matched accordingly. 
-/

def unbox_nat : box_nat → ℕ 
-- box_nat.mk 3     -- pattern matching, unification
| (box_nat.mk n) := n

#eval unbox_nat aBox

/-
When you use the "structure" syntax, Lean
generates a projection (accessor) function
for each field automatically.
-/

#eval box_nat.val aBox
#eval aBox.val     -- Preferred notation




/-
Polymorphic types
-/

/-
We immediately see the same problem 
as with functions: the need for a many 
variants varying only in the type of
value "contained in the box".

The solution is analogous: make our
type polymorphic by having it take a
type-valued parameter and by making
the value it contains of the type 
that is the value of that parameter.
-/

structure box (α : Type) : Type :=
/-mk ::-/
(val : α)

#check box 

def nat_box : box nat := box.mk 3
def bool_box : box bool := box.mk bool.tt

#check nat_box

#check box

def str_box : box string:= box.mk "Hello, Lean!"
def bool_box' := box.mk bool.tt

#eval nat_box.val
#eval str_box.val
#eval bool_box.val

def fun_box : box (nat → nat) := box.mk (nat.succ)

def crazy_box : box (box (nat → nat)) := box.mk (box.mk nat.succ)

#check crazy_box
def f : ℕ → ℕ := (box.val) fun_box
#eval f 5

#check nat → nat 
#check nat.succ
#eval nat.succ 4

/-
Polymorphic product types with two 
fields -- the type of ordered pairs --
and two type parameters accordingly. 
-/

structure prod (α β : Type) : Type :=
(fst : α) 
(snd : β)

-- Self-test: What's the type of prod?

-- "Introduce" some pairs
def pair1 := prod.mk 4 "Hi"

#check pair1
#check prod 

#eval prod.fst pair1
#eval prod.snd pair1

#eval pair1.fst
#eval pair1.snd


def pair2 := prod.mk "Bye" tt

-- "Eliminate" some pairs
#eval pair1.fst
#eval pair1.snd
#eval pair2.fst
#eval pair2.snd


#check prod


structure phythagorean_triple : Type :=
(a : ℕ)
(b : ℕ)
(c : ℕ)
(cert: a*a + b*b = c*c)

def py_tri : phythagorean_triple :=
phythagorean_triple.mk
3 4 5
rfl

#reduce py_tri.cert   -- construct proof that 25 = 25


def py_tri_bad : phythagorean_triple :=
phythagorean_triple.mk
3 4 6
rfl           -- can't construct proof that 25 = 36

-- Try that in mere Haskell. No way!

end hidden
