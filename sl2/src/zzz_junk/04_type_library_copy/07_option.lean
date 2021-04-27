#print option

namespace hidden

/-
Every function in Lean must be total.
That is, there has to be an answer for
*all* values of the argument type. This
constraint presents a problem in cases
where we want to represent *partial*
functions, i.e., functions that are 
not defined for all values of their
argument types.

Suppose for example we want to represent
a partial function from bool to nat that
returns one if a given bool argument is 
bool.tt and that is otherwise undefined.

We can represent this *partial* function 
in Lean as a *total* function from bool
to the type "option nat", a simple sum
of products type, with two variants. The
"none" variant is interpreted as meaning
"no answer, the function is undefined at
the given argument value." By contrast,
the "some" variant boxes a value (a : α)
that holds the result for an argument on
which the function is defined.

Here's a polymorphic option type. 
-/

inductive option (α : Type) : Type
| none : option
| some (a : α) : option

/-
EXERCISE: Represent the partial function
just described using the option type as
just explained. Write your definition in
a separate file, option_test.lean.
-/


end hidden