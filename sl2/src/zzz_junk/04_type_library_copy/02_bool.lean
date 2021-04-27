#check bnot

namespace hidden

/-
The bool data type is a simple,
two-valued (true/false) type. A
set of operations is defined on
values of this type comprising
Boolean algebra. 

EXERCISE: Complete this file as
instructed below.
-/

inductive bool : Type
| tt
| ff

/-
Note: The identifiers ff and tt 
without qualification will refer
to Lean's definitions of these
terms. Use bool.ff and bool.tt
throughout this file. Sorry.
-/

def bnot : bool → bool
| bool.tt := bool.ff    -- 0
| bool.ff := bool.tt    -- 1

def band : bool → bool → bool
| bool.tt bool.tt := bool.tt
| _ _ := bool.ff

/-
EXERCISE: Implement the following
binary boolean operators. Use the
following names for the functions
with the give descriptions.

bor   -- or / disjunction
bxor  -- exclusive or
bimp  -- implies
biff  -- iff / equivalent
bnand -- not and
bnor  -- not or

Use the band, bor, and bnot 
functions to implement your
bnand and bnor functions. You
can look up the truth tables
for functions you're not sure
about.
-/


end hidden