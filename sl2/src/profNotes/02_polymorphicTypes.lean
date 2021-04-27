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

-- Cannot create a value of this type
def x : empty := _

/-
We can define a function from empty to empty,
however, and the reason is a function body is
written based on the *assumption* that is has
received values of specified argument types.
-/ 

def funny : empty → empty
| e := e

/-
Of course there's no way to actually call this
function because there is an argument of type
empty doesn't exist. 
-/

#eval funny _   -- There's no way to fill in _



/-
Start of some new stuff. We will cover the
following additional material on the empty 
type at the beginning of our next class. 
-/

/-
Preliminary: the match...with construct. We
can pattern match on an inductively defined
object (not on functions, for example) using
the match ... with ... end construct in Lean.
When doing so it is both necessary and it is
sufficient to match each possible case that
might occur. In the following example, we
take a romanNumeral and return tt is it's
less than or equal to II, and ff otherwise.
The function is define by cases analysis but
here we use match ... with ... end to do the
case analysis. We introduce match here so we
can use it without further explanation in
the examples that follow.
-/

open romanNumeral

def lessOrEqII (n : romanNumeral) : bool :=
match n with
| I := tt
| II := tt
| _ := ff
end

/-
Even more strangely we can define a function
from the empty type to any other type at all.
-/

-- example 1 (introduces "match ... with")
def weird (e : empty) : nat :=
match e with
-- no cases to consider, so we're done!!!
end

/-
We can even make this function polymorphic
so that it returns a value of any given type
whatsoever.
-/

def strange (α : Type) (e : empty) : α :=
match e with
-- no cases to consider, so we're done!!!
end

/-
These functions look like magic. As long 
as we can come up with a value of type
empty, they can produce values of any type
at all! But there is no magic. 

EXERCISE: Explain why.
-/

/-
Exercise: Can you maybe just create a 
function of type, say, ℕ to empty, and
use it to get an (e : empty) that you
can then use to do magic?

EXERCISE: Explain where you get stuck
if you try.
-/

-- [End of new stuff]

/-
Having seen the empty type (aka ∅) 
we now see sum types with one, two,
and several constructors.
-/

-- unit type (one constructor)
inductive unit : Type   
| star : unit

-- bnit is void in C, Java, etc 

-- bool (two variants)
inductive bool : Type   
| tt : bool
| ff -- ": bool" is inferred

-- A day type: seven variants
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

We generally define functions
that consume values of sum types
by case analysis. To know what
to return, we need to know what
form of value the function got
as an argument. 
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
The left side of a case is 
usually called a pattern. 
Argument values are matched to
patterns in the order in which 
patterns are using what is called
a "unification" algorithm (more
later). Function evaluation 
finds the first pattern in top
to bottom order that matches, 
and return the result obtained 
by evaluating the expression on 
the right hand side of that rule
(or "equation").
-/

#reduce next_day sun
#reduce next_day sat

/-
The _ character can be used in a
pattern to match any value. All
functions in Lean must be total.
We often use _ to cover cases not
covered explicitly by other rules.
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
that takes and bundles up values 
of  zero or more other types into 
records, aka structures. 

In a value of a product type there 
a value for the first field of an
object AND a value for the second 
AND a value for the third, etc. So
PRODUCT, in this sense means, AND.
-/

/-
Note: The empty type can be viewed 
as a product type with zero fields.
-/

/-
We now define a product type with 
one field. 
-/

inductive box_nat' : Type
| mk (val : ℕ) -- 

/--/
To understand such a definition
you need to understand that a
constructor, C, is a specific 
kind of function, namely one
that takes zero or more arguments,
a₀ ... aₙ, and simply constructs a 
term, (C a₀ ... aₙ). You can think
of such a term as a box, labelled
with the constructor name, C, and
containing each argument value
supplied to the constructor.

A value of our box type can thus
be visualized as a box (term) with
a single value, the argument to 
box.mk, inside. 

As usual there are a few syntactic
styles for defining such types. 
We illustrate the syntactic forms
and the general ideas by defining 
a new type, box_nat, a value of
which you can visualize as a box
(or record or structure) with a
single value (field) of type nat.
-/

inductive box_nat'' : Type
| mk : ℕ → box_nat''

structure box_nat''' : Type :=   
mk :: (val : ℕ)

structure box_nat :=  -- readable
(val : ℕ) 

-- Let's create such a value
def aBox := box_nat.mk 3 

-- What does the term look like?
-- Lean prints it using a record notation
#reduce aBox


/- 
Given such a box, we "destructure" 
(open) it using "pattern matching" 
to (1) get at the argument values 
used in its construction, (2) to 
give temporary names to those value
so that we can compute with them. 

Here we see a more interesting form of
unification. The key ideas are (1) the
algorithm determines whether a pattern
matches, (2) it binds specified names
to the values of the fields in the 
object being matched. In general we
use these temporary names to write
expressions that define return values. 
-/

def unbox_nat : box_nat → ℕ 
-- box_nat.mk 3     -- pattern matching
--    |       |     -- n is now bound to 3
| (box_nat.mk n) := n -- return value of n

#eval unbox_nat aBox  -- it works

/-
When you use the "structure" syntax, 
Lean generates a projection (accessor)
function for each field automatically.
Each such function as the same name as
that of the field it projects/accesses.
-/

#eval box_nat.val aBox
#eval aBox.val     -- Preferred notation


/-
Polymorphic types
-/

/-
We now have the same problem we had 
with functions: the need for a many 
copies varying only in the type of
value(s) "contained in the box". For
example we might want a box type a
value of which contains value of type
nat, or of type string, or bool, etc.

The solution is the same: make our
types *polymorphic* by having their 
definitions parameterized by other
types, and by using the *values* of 
these type parameters as the *types*
of other values. 
-/

/-
Here's a polymorphic box type.
-/
structure box (α : Type) : Type :=
(val : α)

/-
box is now a "type builder", a
function that takes a *type), α, 
(e.g., nat, bool) as an argument
and that builds and returns a type,
box α (e.g., box nat, box bool),
whose constructor, mk, take a value
of that type. Here the projection
function, val, is also polymorphic
with an implicit type parameter,
α.
-/

/-
Here are examples where we construct
values of type "box nat" and "box bool"
respectively. Note that box.mk takes no
explicit type argument.
-/
def nat_box : box nat := box.mk 3
def bool_box : box bool := box.mk bool.tt

/-
Tiny note: We defined our own version 
of bool above. If we were to write tt
in this example, we'd pick up Lean's 
tt, not our own, so we write bool.tt
instead, picking up the version of
bool we've defined in this namespace
(hidden). 
-/

/-
So what's the type of box itself? It's
not type, but rather reflects the fact
that box takes a type (of type, Type) as
an argument and returns a type (of type,
Type) as a result.
-/

#check nat_box

-- Example uses of the "box α" type

-- box string
def str_box : box string:= box.mk "Hello, Lean!"
-- box bool
def bool_box' := box.mk bool.tt

#eval nat_box.val
#eval str_box.val
#eval bool_box.val  -- Lean doesn't know how to print 

-- We can also create boxes that contain functions
#check nat.succ
#eval nat.succ 4
def fun_box : box (nat → nat) := box.mk (nat.succ)


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

-- prod "type" has two type arguments
#check pair1
#check prod 

-- polymorphic projection functions   
#eval prod.fst pair1
#eval prod.snd pair1

-- dot notation, like in C, C++, Java, etc
#eval pair1.fst
#eval pair1.snd

/-
A forward-looking example: a structure type
the values of which are pythagorean triples.
The first three fields are the lengths of 3
sides of a triangle. The value of the last
field is a proof (whatever that is in Lean)
that the values of the first three fields
satisfy the condition of being such a triple.
What this means is that you simply cannot
construct a triple of this form without a
proof that it really is Pythagorean. The 
*type* of proof required as a value in the
last field is *uninhabited* (empty) if the
three numbers don't add up right.
-/
structure phythagorean_triple : Type :=
(a : ℕ)
(b : ℕ)
(c : ℕ)
(cert: a*a + b*b = c*c)

/-
Without explaining what rfl does exactly,
here's a case where the require proof is
constructed automatically (by rfl).
-/
def py_tri : phythagorean_triple :=
phythagorean_triple.mk
3 4 5
rfl

/-
Here, however, there is no such proof, 
so its construction fails, and the bug
in our argument values is revealed by
this failure.
-/
def py_tri_bad : phythagorean_triple :=
phythagorean_triple.mk
3 4 6
rfl  -- can't construct proof of 25 = 36

-- Try that in Java or mere Haskell!

end hidden
