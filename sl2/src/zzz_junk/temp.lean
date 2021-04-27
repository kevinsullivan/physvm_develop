/-
Namespaces
-/

namespace hidden    -- "hidden" has no special meaning

/-
Polymorphism
-/


/-
Polymorphic Functions
-/

-- A problem

def id_nat : nat → nat := 
  λ n, n

def id_string : string → string := 
  λ n, n

def id_bool : bool → bool :=
  λ n, n

/- A solution

Parametric polymorphism means (1) one of 
the arguments to a function is a type, and
(2) the *types* of the remaining arguments 
can depend on the *value* of that earlier
argument. To make this possible Lean treats
types as values (terms), too.
-/

-- types are literal terms
#reduce bool  
#reduce string
#reduce nat

-- As such, each type itself has a type
#check bool
#check string
#check nat

/-
The idea, then, is that we can pass a type as
a value to a function and then use the *value*
of that argument as the *type* for arguments
that follow. 

For this to work, we need to *bind a name* to
the value of the earlier type parameter, so 
that we can then use that name to specify the
types of arguments that might follow.

To achieve such a binding, we use the binding
construct, Π or ∀ (they're equivalent), each of
which has the effect of binding a name to an 
*assumed* value, here one that is assumed to 
to be given as an argument.  
-/

def id' : Π (α : Type), α → α := 
  λ α, 
    λ n, 
      n

def id'' : Π (α : Type), α → α
| α n := n

def id''' (α : Type) (n : α) : α := n

#eval id' ℕ 3
#eval id'' string "Hello, Lean!"
#eval id''' bool tt

-- Lean can often infer type arguments from context
#eval id' _ 3
#eval id'' _ "Hello, Lean!"
#eval id''' _ tt

-- We can go even further and tell Lean to infer them silently

def id { α : Type } (n : α) : α := n

#eval id 3
#eval id "Hello, Lean!"
#eval id tt

/-
We now have a polymorphic function. It looks like it's
not strongly typed, in the sense that it can be applied
to arguments of different types; but it is still strongly
typed. It's just that the *types* of some later arguments
depend on the *values* of earlier, type-valued arguments.
-/

/-
When a function is defined to take an argument implicitly,
the argument cannot be given explicitly.
-/

#check id 3
#check id nat 3

/-
Sometimes, though, Lean will lack sufficient context to
infer the intended type argument.
-/

#eval id _

/-
In such cases, we might need to turn off implicit type
inference. For that, we use the @ symbol.
-/

#eval @id nat _

/-
What is the type of our polymorphic function?
-/

#check id     -- unknown type to unknown type
#check @id    -- given type argument, α, α → α

/-
Polymorphic types
-/

/-
Just as functions can be polymorphic -- i.e.,
take type values on which the types of other
elements depend, types can be polymorphic, too.

You're probably already familiar with this 
idea from languages like Java and C++. Name
some polymorphic types in these languages?

We explain the idea in a few steps

1. constructors with arguments
2. pattern matching arguments
3. the same problem of duplication
4. solving it with parametric polymorphism
-/

-- #1: constructors with arguments

/-
An abstract data type, with (1) a constructor 
that lets us store a natural number "in a box," 
as a field of a term of type box_nat; and (2)
a function that lets us "destruct" such a "box"
value to get at and return the natural number
value in that field.  
-/
inductive box_nat : Type
| wrap (n : ℕ) : box_nat  --

def unbox_nat : box_nat → nat
| (box_nat.wrap n) := n

-- Let's test it out
def box_3 := box_nat.wrap 3
def box_5 := box_nat.wrap 5

#eval unbox_nat box_3
#eval unbox_nat box_5

/-
The same "template" but now for string values
-/
inductive box_string : Type
| wrap (n : string) : box_string

def unbox_string : box_string → string
| (box_string.wrap n) := n


/-
The same "template" but now for bool values
-/
inductive box_bool : Type
| wrap (n : bool) : box_bool

def unbox_bool : box_bool → bool
| (box_bool.wrap n) := n

-- We see the problem once again

/-
A polymorphic box type
-/

inductive box (α : Type) : Type
| wrap (n : α) : box  -- type param implicit

def unbox : Π {α : Type}, box α → α 
| _ (box.wrap n) := n -- _ in pattern is wildcard

def box_4 := box.wrap 4
def box_tt := box.wrap tt
def box_hi := box.wrap "Hi!"

#eval unbox box_4
#eval unbox box_tt
#eval unbox box_hi


/-
A little more Lean

A "structure" is a special case of an inductive
data type: one with just one constructor, with
named fields, and with auto-generated accessors.
Here's the same polymorphic box type defined as
a "structure".
-/

structure bx (α : Type) :=
(val : α)  -- default constructor called "mk"

-- create an object
def bx_nine := bx.mk 9
def bx_joy := bx.mk "Joy"

-- accessors have field names
#eval bx_nine.val
#eval bx_joy.val

/-
What looks like accessing data fields of an 
"object" (structure) using "dot" notation is
really just application of a function that
(1) destructures and object, and (2) returns
of of its component field values. The benefit
of using "structure" to define a type is that
we don't have to explicitly define accessor,
or "projection", functions.
-/

#eval bx.val bx_nine
#eval bx.val bx_joy
--    ^^^^^^
-- field names are al projection func names 

end hidden