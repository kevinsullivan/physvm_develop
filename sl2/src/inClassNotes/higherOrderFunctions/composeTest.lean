/-
Let's build up to notion of 
higher-order functions.
-/

namespace hidden

-- Increment functions

def inc (n : nat) := n + 1
def sqr (n : nat) := n * n

def incThenSqr (n : nat) := sqr (inc n)
/-
  36 <-- sqr <-- inc <-- 5

Think of data flowing right to left
through a composition of functions:
given n (on the right) first send it
through inc, then send that result
"to the left" through sqr.
-/


def sqrThenInc (n : nat) := inc (sqr n)
/-
  26 <-- inc <-- sqr <-- 5
-/

#eval incThenSqr 5
#eval sqrThenInc 5


/-
A diagram of the evaluation order

  36 <-- (sqr <-- (inc <-- 5))
  26 <-- (inc <-- (sqr <-- 5))
-/

/-
Regrouping parenthesis tells us that
sending the input through two functions
right to left is equivalent to running
it through a single function, one that
"combines" the effects of the two.
 
  36 <-- (sqr <-- inc) <-- 5)
         ^^^^^^^^^^^^^
          a function

  26 <-- (inc <-- sqr) <-- 5)
         ^^^^^^^^^^^^^
          a function
-/

/-
  36 <-- (compose sqr inc) <-- 5)
  26 <-- (compose inc sqr) <-- 5)
         ^^^^^^^^^^^^^^^^^
            a function
-/
/-
  36 <-- (compose sqr inc) <-- 5)
  26 <-- (compose inc sqr) <-- 5)
          ^^^^^^^ 
    higher-order function
-/

/-
Remember that a lambda term is 
a literal value that represents
a function. What's special about
the form of data is that it can
be *applied* to an argument to
produce a result.

A higher-order function is just 
a function that takes a lambda 
term (aka "a function") as an 
argument and/or returns one as
a result. In particular, we will
often want to define functions
that not only take "functions"
as arguments but that return 
new functions as results, where
the new functions, *when applied*
use given functions to compute
results. 

Such a higher-order function is a 
machine that takes smaller data
consuming and producing machines
(functions) and combines them into
larger/new data consuming and 
producing machines. Composition 
of functions is a special case in
which a new function is returned
that, when applied to an argument,
applies each of the given functions
in turn.  
-/

/-
  36 <-- (sqr ∘ inc) <-- 5)
  26 <-- (inc ∘ sqr) <-- 5)
-/

/-
Can we write a function that
takes two smaller functions,
f and g, and that returns a
function, (g ∘ f), that first 
applies f to its argument and
then applies g to that result?

Let's try this for the special
case of two argument functions,
such as sqr and inc, each being
of type nat → nat.
-/

def compose_nat_nat  (g f: ℕ → ℕ) : 
  (ℕ → ℕ) :=
_  


-- let's test it out
#eval (compose_nat_nat sqr inc) 5
--    ^^^^^^^^^^^^^^^^^^^^^^^^^ function!
def sqrinc := compose_nat_nat sqr inc
#eval sqrinc 5

#eval (compose_nat_nat inc sqr) 5
def incsqr := compose_nat_nat inc sqr
#eval incsrq 5
/-
Suppose we want to compose functions
that have different types. The return
type of one has to match the argument
type of the next one in the pipeline.
Parametric polymorphism to the rescue.
-/
def compose_α_β_φ  { α β φ : Type } 
  (g : β → φ) (f: α → β) : α → φ :=
_ 

#eval (compose_α_β_φ sqr string.length) "Hello!"

/-
The previous version works great as
long as the functions all takes values
of types, α, β, and φ, of type Type.
But in general, we'll want a function
that can operate on functions that 
take arguments and that return results
in arbitrary type universes. So here,
then is the most general form of our
higher-order compose function.
-/

universes u₁ u₂ u₃  -- plural of universe

def compose 
  {α : Type u₁} 
  {β : Type u₂} 
  {φ : Type u₃}  
  (g : β → φ) 
  (f: α → β) : 
  α → φ :=
fun a, g (f a) 
/-
Return a *function* that takes
one argument, a, and returns the
result of applying g to the result
of applying f to a.
-/

def incThenSqr' := compose sqr inc 
def sqrThenInc' := compose inc sqr 
def sqrlen := compose sqr string.length

#eval incThenSqr 5  -- expect 36
#eval incThenSqr 5  -- expect 26
#eval sqrlen "Hello!"

/-
Lean implements function composition
as function.comp, with ∘ as an infix
notation for this binary operation.
-/

#check function.comp 
#check @function.comp 

/-
function.comp : 
  Π {α : Sort u_1} {β : Sort u_2} {φ : Sort u_3}, 
    (β → φ) → (α → β) → α → φ
-/

/-
                Prop (Sort 0) -- logic
Type (Type 0)   Sort 1        -- computation
Type 1          Sort 2
Type 2          Sort 3
etc    
-/

universes u₁ u₂ u₃ 

-- introduce some local assumptions
variables (f : Sort u₁ → Sort u₂) (g : Sort u₂ → Sort u₃)

#check function.comp g f
#check g ∘ f



end hidden