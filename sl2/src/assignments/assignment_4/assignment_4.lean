/-
1. Write a polymorphic function, someSatisfies, 
that takes a a predicate function, p, of type 
α → bool, and list of values of type α (a type
parameter), and and that returns true (tt) if 
and only if there is some value, v, in the list, 
for which (p v) is true (tt). Your implementation
must use list_map to convert the given list of α 
values to a list of bool values, which it must
then pass to a helper function, the job of which
is to return true (tt) if and only there is some
tt value in the list.
-/

/-
2.  Write a polymorphic function, allSatisfy, 
that takes a predicate function, p, of type 
α → bool, and list of values of type α (a type
parameter), and and that returns true (tt) if 
and only if for every value, v, in the list, 
(p v) is true (tt). Your implementation must 
use list_map to convert the given list of α 
values to a list of bool values, which it must
then pass to a helper function, the job of which
is to return true (tt) if and only every value
in the list is tt. 
-/

/-
3. Write a function called simple_fold_list.
It has a type parameter, α, and takes (1) a
binary function, f, of type α → α → α, (2) a 
single value, i, of type α, as a list, l, of
type list α The purpose of simple_fold_list 
is to "reduce" a list to a single value by
(1) returning i for the empty list, otherwise
(2) returning the result of applying f to the
head of the list and the reduction of the rest
of the list. 

Here are two examples:

simple_fold_list nat.add 0 [1,2,3,4,5] = 15
simple_fold_list nat.mul 1 [1,2,3,4,5] = 120
-/

/-
4. Write an application of simple_fold_list to
reduce a list of strings to a single string in
which all the individual lists are appended to
each other. You can use ++ (or string.append) to
append strings without writing your own function
to do so. 

For example, reduce ["Hello", " ", "Lean!"] to
"Hello, Lean!"
-/

/-
5. Re-implement here your helper functions from
questions 1 and 2 using simple_fold_list.
-/

/-
6. This question asks you to understand how to
write inductive families in a slightly different
way than we've seen. Here's the definition of an
inductive family, ev, indexed by natural numbers.
Read the definition. We explain it further below.
-/

inductive ev : ℕ → Type
| ev_base : ev 0
| ev_ind  {n : nat} (evn : ev n) : ev (n + 2)

open ev


/-
The first line of this definition explains that
ev is a family of types indexed by values of type
nat. In other words, for every nat, n, there is
a corresponding type, ev n. In particular, there
are types, ev 0, ev 1, ev 2, ev 3, etc.

The next two lines, the constructors, explain how
values of all of these types can be constructed.

The first constructor, ev_base, is declared to 
be a term (value) of type ev 0. You can think
of this term as being our version of "evidence"
that "zero is even".

The second constructor takes two arguments. The
first implcit argument is a natural number, n.
The second, evn, must be a term of type (ev n),
*for that particular n* (dependent typing here).
Finally, focus on this, a term (ev_ind n evn) is
of type (ev (n+2)). You can think of such a term
as being our form of evidence that n+2 is even. 
-/

/-
6A. Complete the following definitions by filling
in the placeholders with terms of the indicated
dependent types. Use the available constructors
to create these values. (Remember that the first
argument to ev_ind is impliict, and not that it
can be inferred from the second argument.)
-/

def ev0 : ev 0 := _
def ev2 : ev 2 := _
def ev4 : ev 4 := _
def ev6 : ev 6 := _
def ev8 : ev 8 := _
def ev10 : ev 10 := _

/-
6B. You should have been able to give values for 
each of the preceding six types ev 0, ..., ev 10.
What single word can you use to indate that each
of these types has at least one value?
-/


/-
6C. Try to give values for each of the types in
the following definitions. Explain as clearly and
in as few words as you can why you won't be able
to do this, and state the word that best describes
each of these types, in relation to the fact that
these types have no values.
-/

def ev1 : ev 1 := _
def ev3 : ev 3 := _
def ev5 : ev 5 := _

/-
6D. Define an inductive family, odd n, indexed by
natural numbers, such that the type for every odd
number has at least one value, and the types for
even numbers have no values. Then show that you 
can complete the preceding three definitions if you
replace ev by odd.
-/

inductive empty' : Type

/-
7. As you know, the type, empty, is uninhabited.
That is, it has no values. So what does it tell
us if we can define a function of a type that
"returns a value of type empty?"
  
Show that there is a function, let's call it 
foo, of type ev 1 → empty. Then show there's a 
function, let's call it bar, of type ev 3 → empty. 
Finally, show that there's a function, baz, of 
type ev 5 → empty. (NB: To show that there is a
function of a given type, you must write some
(any) function of that type. What it actually 
does doesn't matter.)

Once you've done the preceding exercises,
write a short answer (in English) to the
question at the beginning of this problem.
-/

def foo : ev 1 → empty :=
λ (e : ev 1), _ -- match ... with ... end
  -- for every possible form of e, return a value of type empty

/- 8. Define evdp to be a sigma (dependent 
pair) type, a value of which has a natural
number, n,  as its first component, and a 
value of type, ev n, as its second. Then 
define evp0, evp2, and evp4 to be values
of this type, whose first elements are,
respectively, 0, 2, and 4.
-/

-- hint
#check Σ (n : nat), ev n

-- Your answers here

/- 9. Write a function, mkEvp, that takes 
a argument, mn, of type nat, iplicitly, and 
an argument, nEv ot type, ev n, and that 
returns a value of type evdp (from the last
problem). Then briefly answer the question, 
in what sense does mkEvp have a dependent
function type? 
-/

-- Your answers here

