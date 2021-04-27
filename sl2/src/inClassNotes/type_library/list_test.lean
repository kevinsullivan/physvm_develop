import .list

namespace hidden

-- list is polymorphic
#check list nat         -- nat lives in Type
#check list bool        -- bool lives in Type
#check list Type        -- Type lives in Type 1
#check list (Type 1)    -- Type 1 lives in Type 2

/-
Some lists of nats
-/

#eval list.nil        -- can't infer α 
#eval @list.nil nat   -- can't infer α 
#eval (list.nil : list nat)

/-
Top-down (outside-in) refinement
-/

def lnat0 : list nat := list.nil 

def lnat1 : list nat :=
  list.cons
    (_)
    (_)

def lstr1 : list string :=
  list.cons 
    (_)
    (list.cons
      (_)
      (list.nil)
    )
/-
        cons
        /  \
      "hi" cons
           /  \
         "ho" ...
-/

-- FUNCTIONS

def head { α : Type } : list α → option α 
| list.nil := none
| (list.cons h t) := some h

def tail { α : Type } : list α → option (list α) 
| list.nil := none
| (list.cons h t) := some t

-- recursive definition of length (by cases)
def length {α : Type} : list α → nat
| list.nil := 0 
| (list.cons h t) := (_) + 1   -- length in context

def append {α : Type} : list α → list α → list α
| list.nil         m := _
| (list.cons h t)  m := _

def pure {α : Type} : α → list α 
| a := list.cons a list.nil

def reverse {α : Type} : list α → list α 
| list.nil := list.nil
| (list.cons h t) :=  _

#eval reverse (list.cons 1 (list.cons 2 list.nil))

end hidden

/-
From here on, we use Lean's identical
definition of the list type, but we 
gain the benefit of additional notation.
-/

/-
NOTATION
-/

#eval list.cons "hi" (list.cons "ho" list.nil)
#eval ["hi", "ho"]
#eval list.cons "hi" ["ho"]
#eval "hi"::["ho"]
#eval 
  let s : string :=
    let a := ["hi","ho"] 
    in 
      (match a with 
        | list.nil := "oops"
        | (h::t) := h 
      end) 
  in s ++ "!"

-- more examples
#eval [1,2,3,4,5]
#eval 1::[2,3,4,5]
#eval 1::2::3::4::5::list.nil


def head { α : Type } : list α → option α 
| list.nil := none
| (h::t) := some h

def tail { α : Type } : list α → option (list α) 
| list.nil := none
| (h::t) := some t

-- recursive definition of length (by cases)
def length {α : Type} : list α → nat
| list.nil := 0 
| (h::t) := (_) + 1   -- length in context

#eval list.append ["Hi","Ho"] ["!"]
#eval ["Hi","Ho"] ++ ["!"]

#check @pure list
#eval (pure 5 : list nat)
#eval (pure 5 : option nat) -- whoa (later)

def reverse {α : Type} : list α → list α 
| list.nil := list.nil
| (h::t) :=  _    -- use nice notation here

universe u

/- 
HIGHER ORDER FUNCTIONS
-/

/-
Suppose we want to map a list of
strings to a list of bools, where
each bool is tt if the length of 
the corresponding string is even,
and false otherwise.
-/

def strlist := ["Hello", "There", "Lean"]

def map_ev_string_bool :
  list string →
  list bool 
| list.nil := list.nil
| (h::t) := (h.length%2=0)::_

def map_odd_string_bool :
  list string →
  list bool 
| list.nil := list.nil
| (h::t) := (h.length%2=1)::_

def map_string_bang_string :
  list string →
  list string 
| list.nil := list.nil
| (h::t) := (h++"!")::(map_string_bang_string t)

#eval map_string_bang_string strlist

/-
Dimensions of variation?
-- argument list element type, α 
-- result list element type, β 
-- function used to transform α → β 
-/
def map_list {α β : Type u} : 
    (α → β) → list α → list β 
| f list.nil := list.nil
| f (h::t) := (f h)::(map_list f t)

#eval map_list 
        (λ (s : string), s.length)
        (strlist)

#eval map_list 
        (λ (s : string), (s.length%2=0:bool))
        (strlist)

def exclafy : list string → list string :=
  map_list (λ (s : string), s++"!") -- arg

#eval exclafy ["Whoa","That","Is","COOL"] 

/-
Define reduce, or fold, over a list. 

Let's start with an example. Suppose
we're given a list of strings and we
want to know if they are all of even
length. What we need is a function,
allEvenLength : list string → bool,
that returns tt iff all strings in
the list have even length.

Let's do an informal case analysis:

First we consider the case where the
given list of strings, l, is not empty. 
In this case it has the form (h::t),
with (h : string) and (t : list string).
And in this case, every string in the
list will have even length iff (1) h 
is of even length *AND* every string 
in the tail, t, of l, also has even
length.

Now consider the case where l is nil.
What Boolean value do we return? One
might guess false ... incorrectly.

Suppose our function returned false
(ff) for the empty list. Consider a
case where l = ["Hi"]. That is, the
list, l = (list.cons "Hi" list.nil).

The list is non-empty, so the first
rule applies: return the AND of two
Boolean values: one for "Hi" and one
for the rest of the list. For "Hi"
we will get true, as "Hi" has even
length, so our result will have to
be (tt ∧ X), where X is the result
for the rest of the list. But here
the rest of the list is empty. So
what *must* R, the result for the
empty list, be for the function to
return the right result, tt (as all
strings in the list are even length)?

Clearly the answer must be true (tt).
What would happen if it were ff?

So now we have our algorithm!
-/

-- first a predicate function

def isEvenStr (s : string) : bool :=
  (s.length % 2 = 0)

def allEvenStr : list string → bool 
| list.nil := tt
| (h::t) := band (isEvenStr h) (allEvenStr t)

#eval allEvenStr []
#eval allEvenStr ["Hi"]
#eval allEvenStr ["Hi!"]
#eval allEvenStr ["Hi","There!"]
#eval allEvenStr ["Hi","Ho!"]

/-
Now suppose we want to know if there
is *at least* one string of even length
in any given list of strings. 

Again we do a case analysis.

There is at least one even-length 
string in a non-empty list, l = h::t,
iff h is of even length OR there is at
least one even-lenght string in the 
rest of the list.

Now suppose t is the empty string.
What result must be returned for the
function to work. Consider the case
where l = ["Hi!"] = (cons "Hi" nil).
The correct answer here is (ff ∨ X),
with the ff because "Hi!" is not of
even length, and X is the answer for
the empty list. To get the correct
answer, it must be that X = ff. So
now again we have our algorithm.
-/



/-
The key idea both here and in the
preceding example is that the answer
for the empty list must leave the
result for the preceding elements
unchanged. The result must be the
*identity element* for the Boolean
operator being used to combine the
values for the head and rest of the
list. 

The identity element for Boolean and
is tt, and for  Boolean or it is ff.

∀ (b : bool), b ∧ tt = b
∀ (b : bool), b ∨ ff = b

We can see these propositions are true
by case analysis. Case 1: b = tt. In
this case b ∧ tt = tt and b = tt so
b ∧ t = b. Exercise: Finish up.
-/

def someEvenStr : list string → bool 
| list.nil := ff
| (h::t) := bor (isEvenStr h) (someEvenStr t)

#eval someEvenStr []
#eval someEvenStr ["Hi"]
#eval someEvenStr ["Hi!"]
#eval someEvenStr ["Hello","Lean"]
#eval someEvenStr ["Hello","Lean!"]

/-
Now a key observation: Our two functions
are very similar, varying in only a few
dimensions. Let's factor dimensions of 
variation into parameter to generalize
our definition.

First, we want to be able to operte on
lists of values of any type, not just
strings. Let call the list element type
α. 

Second, in general, we want to reduce
a list (l : list α) to a value of some
other type, let's call it β, just as in 
our examples we reduced lists of values
of type α = string to a final result of
type β = bool.

Third, we need a function to compute
the answer for a non-empty list (h::t) 
where (1) (h : α), (2) the result for
the rest of the list is of type β, and
(3) the final combined result is of type
β. The type of this reducing function is
thus α → β → β. 

Finally, we need a result value for the
empty list. This value obviously has to
be of type β.


Those are our parameters!

Given: 
{ α : Type u}
{ β : Type u}
( f : α → β → β )
( id : β)
( l : list α)
Compute result : β
-/

-- By case analysis on the list l
def fold { α : Type u} { β : Type u} :
( α → β → β ) → β → list α → β 
| f id list.nil := id
| f id (h::t) := f h (fold f id t)

-- allEven

def allStrCombine : string → bool → bool
| s b := band (isEvenStr s) b

def allEvenStr' (l : list string) : bool :=
  fold allStrCombine tt l 

def someStrCombine : string → bool → bool
| s b := bor (isEvenStr s) b

def someEvenStr' (l : list string) : bool :=
  fold someStrCombine ff l 

#eval allEvenStr' []
#eval allEvenStr' ["Hi"]
#eval allEvenStr' ["Hi!"]
#eval allEvenStr' ["Hi","There!"]
#eval allEvenStr' ["Hi","Ho!"]#eval someEvenStr []
#eval someEvenStr' ["Hi"]
#eval someEvenStr' ["Hi!"]
#eval someEvenStr' ["Hello","Lean"]
#eval someEvenStr' ["Hello","Lean!"]


#eval fold nat.add 0 [10,9,8,7,6,5,4,3,2,1]
#eval fold nat.mul 1 [10,9,8,7,6,5,4,3,2,1]

#eval fold string.append "" ["Hello, ", "Lean. ", "We ", "love ", "you!"]



/-
Given a predicate function on the type of
element in a list, return the sublist of
elements for which predicate is true.

Define filter by case analysis with one
case a base case and the other case using
"structural recursion" on list argument.

An opportunity to introduces if/then/else 
expression in Lean.
-/

def filter' {α : Type u} : 
  (α → bool) → list α → list α 
| f list.nil := list.nil
| f (h::t) := if (f h) 
              then h::(filter' f t) 
              else (filter' f t)

/-
Take opportunity to introduce let
bindings. Binds name to result of
evaluation, then evaluates expr in
context of that additional binding.
-/
def filter {α : Type u} : 
  (α → bool) → list α → list α 
| f list.nil := list.nil
| f (h::t) := let restOfResult := (filter f t) 
              in
                if (f h) 
                then h::restOfResult
                else restOfResult

def isEven (n : nat) : bool := n%2 = 0

#eval filter isEven []
#eval filter isEven [0,1,2,3,5,6,7,9,10]

/-
Note: the body of a let can use another
let. That is, let bindings can be chained.

let x := 1 in
  let y := 2+3 in
    let z := 3*4 in
      x + y + z

To what value does this expression reduce?

-/
