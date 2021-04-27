import .option

namespace hidden 

/-
Every function in Lean must be total.
That is, there has to be an answer for
*all* values of the argument type.

Examples: 

    Total function, f, from bool to nat
    ff --> 0
    tt --> 1

    Partial function, p, from bool to nat
    ff ---> 
    tt --> 1
-/

-- We can express f in Lean like this
def f : Π (b : bool), nat
| ff := 0
| tt := 1

-- But if we try p the same way it's an error
def p : bool → nat
| tt := 1

/-
While the totality of "functions" in Lean
isn't obvious from the function type syntax
(α → β), it becomes clear when you see what
(α → β) really means.
-/

#check bool → ℕ           -- Function types
#check Π (b : bool), nat  -- Are Pi types
#check ∀ (n : bool), nat  -- ∀ means same thing

/- Function types in CL are Pi types

A Pi type, (Π (a : α), β), is a 
function type. As such, a value,
f, of this type (aka a "function"
in Lean) associates with *every* 
value (a : α) a corresponding value, 
(f a) : β. 

A Π type is thus a kind of product
type, in the sense that any value 
("function") of this type implicitly
specifies a set of pairs, (a, f a), 
containing exactly such pair for 
each and every value, (a : α). 

You can also visualize a value of
a Π type as attaching some value of
type β to every value of type α, by
means of a string, or "fiber." 
  
If you really get into this stuff, 
you might even use "fibration" to 
describe what a value of the type
(Π (a : α), β) does with α.

Finally, the especially curious
student will ask, Why does a Π 
type bind a name, here a, to the
argument? What's wrong with just
leaving it unnamed, as when using
the notation, α → β? It's as if
we'd written (a : α) → β. What's
up with that?

The answer is, it's useful when
we want the *type* of the return
value to depend on the value of 
the argument, a! A Π type can
express this idea. Consider an
example:

Π (n : ℕ), seq n

This type represents the type 
of function that takes a natural
number n and returns a sequence
*of length n*, where the length
of the sequence is part of its 
*type*.

Welcome to the type theory of
Lean in its full generality. We
don't need "dependent types" at
this point, but we will soon,
so it's good idea to get a first
glimpse at the idea here.

For now, we need to get back
to the option type and its use.
-/

/- Examples of partial functions

Now suppose that we want to 
represent a partial function, f, 
from bool to nat, in Lean, where 
f is define as follows:

b  | f b
ff |  0
tt |  _


While f has *some* value for ff, 
it has *none* for tt. In the lexicon
of everyday mathematics that makes
it a *partial* function.

Here's another example: a partial
function from nat → nat that's just
like the identity function except
it's defined only for even numbers.

n  | f n 
---| -----
0  | 0
1  | _
2  | 2
3  | _
4  | 4
5  | _
&c | &c

 
Yet another is the square root where
the *domain of definition* and the 
*co-domain* are the real numbers, ℝ. 

Here the function is partial because 
the real-valued square root function 
is not defined for every value in the 
domain of definition, which includes
the negative reals, on which the real
square root function is undefined. 

Note that if we defined the domain
of definition of a *similar* square
root function to be the non-negative
real numbers, then that function is
total, because it's defined for every
value of its domain of definition. 
-/

/-
So let's talk about functions in the
usual mathematical (set theoretical as
opposed to type theoretical) sense? 
What are the essential characteristics
of a function, and how can we understand
totality and partiality in these terms?

A function in set theory, f, is defined
by a triple, (α, β, R), where 

- α, a set, is the *domain of definition* of f 
- β, a set, is the *co-domain* of f,  
- R ⊆ α ⨯ β is a binary relation on α and β 

By a binary relation on sets α and β we just
mean a set of pairs (x, y) where x values 
are in α and y values are in β.

Example: our even identity function above
is (ℕ, ℕ, {(0,0),(2,2),(4,4),etc.})

The *domain* of f is the subset of values
in the domain of definition on which f is
defined. 

The domain of definition of our even 
identity function is the set of all 
natural numbers, {0, 1, 2, 3, ...}, 
but the *domain* of the funciton is
just {0, 2, 4, etc.}, the even numbers. 

dom f = { x ∈ α | ∃ y ∈ β, (x, y) ∈ R } 

The *range* of f is the subset of all 
values in the co-domain that are values 
of (f x) for *some* element, x, in dom f.

The codomain of our even identity function
is the natural numbers but the range is
just the set of even natural numbers.

ran f = { y ∈ β | ∃ x ∈ α, (x, y) ∈ R) }
-/



/-
How can we represent mathematically
partial functions in Lean (or other
constructive logic proof assistant)
when all "functions" must be total?

Consider our partial function from
bool to nat. First we represent 
the domain of definition set, the
booleans, as the inductive type, 
bool. We will need to return *some* 
value of some inductive type for
each value (a : α): a value for tt
and a value for ff. We *cannot* 
specify *bool* as the return type,
because then we'd be defining a
total function. What we need is a
new type that in a sense augments
the bool type with on additional
element that we can use to signal
"undefined". That is the purpose
of the polymorphic option type
builder. It allows us to return
either *some (b : β)* or *none*.
We can then represent our partial
function, f, from bool to nat, as 
a total function, f', from bool to 
*option nat*: one  tht returns 
*none* when applied to a value, b, 
on which f is not defined, and that 
otherwise returns *some n*, where 
n = (f b).
-/

/-
See option.lean for its definition.
It's defined there just as it is
in the standard Lean libraries, so
after these exercises you can use 
it without having to define it for
yourself.
-/

def pFun : bool → option ℕ 
| tt := option.none
| ff := option.some 0

#reduce pFun tt
#reduce pFun ff


def evenId : ℕ → option ℕ :=
λ n, 
  if (n%2=0) 
  then (option.some n) 
  else option.none

#reduce evenId 0
#reduce evenId 1
#reduce evenId 2
#reduce evenId 3
#reduce evenId 4
#reduce evenId 5

/-
In Lean, we represent the sets, α and β,
as types, and a total function, f, as a
value of type Π (a : α), β, i.e., (α → β). 

This type means for every (a : α) there 
is a corresponding value, (f a) : β.  We 
cannot represent a *partial* function, 
(α, β, R) using a Π type on α and β. Our
workaround for now is to represent such
a function instead as a function of type 
Π (a: α), option β, i.e., (α → option β)
as we've described.
-/


end hidden

