/-
Identity functions for types nat, string, and bool.
An identity function takes and argument and returns
it unchanged.
-/


def id_nat : nat → nat :=
  λ n, n 

-- quick reminder on alternative syntax

-- cases
def id_nat' : nat → nat 
| n := n

-- c-style
def id_nat'' (n : nat) : nat := n

-- back to main point
def x : nat := 5
def id_string : string → string :=
  fun (s : string), s 
  
def id_bool : bool → bool :=
  λ n, n 

/-
Parametric polymorphism: types are
terms (values), too, and so can be
given as arguments to functions.
-/

-- Use #check to see the type of any term

#check 1
#check "Hello"
#check tt

/- 
Types are terms, too. As such, every type
has a type. All of the usual computational
types, and any additional ones you might
define, are of type, Type. It's important
to understand this now.
-/

#check nat 
#check string
#check bool

/-
Here's a polymorphic identity function. The
"Π (α : Type), α → α" is the type of this
function. You can read it like this: Given
any type, α (such as nat or bool or string),
the function is of type α → α. So if the value
of the first argument, α, is bool, for example,
then the the rest of the type is bool → bool.
-/

def id1 : Π (α : Type), α → α := 
  λ α,
    λ a,
      a

-- Alternative syntax

def id2 (α : Type) (a : α) := a

def id3 : Π (α : Type), α → α 
| α a := a

-- tests
#eval id1 bool tt               -- expect tt
#eval id1 string "Hello, Lean!" -- expect "Hello..."
#eval id1 nat 5                 -- expect 5


/-
Type inference
-/

-- Lean can infer the value of α from the second argument
#eval id1 _ tt                -- α must be bool
#eval id1 _ "Hello, Lean!"    -- α must be string
#eval id1 _ 5                 -- α must be nat

-- Exercise: Become fluent quickly with these notations

/-
Implicit type inference

You can ask Lean to infer values automatically. To do this
put curly braces rather than parentheses around an argument.
-/

def id4 : Π { α : Type }, α → α := 
  λ α,
    λ a,
      a

def id5 { α : Type } (a : α) : α := a

def id6 : Π { α : Type }, α → α
| α a := a

-- Compare with preceding examples
#eval id4 tt                -- α must be bool
#eval id5 "Hello, Lean!"    -- α must be string
#eval id6 5                 -- α must be nat

-- You can turn off implicit arguments with @

#eval @id4 bool tt                  
#eval @id5 string "Hello, Lean!"    
#eval @id6 nat 5                    


