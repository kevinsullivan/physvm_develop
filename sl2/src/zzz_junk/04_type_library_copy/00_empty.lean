namespace hidden

/-
The empty data type has no
values/constructors at all.
This fact becomes interesting
and useful when one performs
a case analysis on values of
this type, as there are no
cases to consider. 
-/
inductive empty : Type

/-
Exercise: Show that you can
implement a function, e2n, that
takes (assumes it's given) an
argument, e, of type empty and
that then uses match/with/end
to "eliminate" e and to return
without returning any particular
value of type nat.
-/

/-
Lean's "match...with...end"
function.
-/



end hidden