namespace hidden

/-
The unit type is a computational 
data type inhabited by just one 
constant, in lean called *star*. 

A value of this type is available
at all times and doesn't carry any
information at all (wheras a value
of type bool carries one bit).

There's not much reason ever to 
pass a unit value to a function,
as it conveys no useful information.

The place where the unit type is
of use is as the return type of a
function whose only purpose is to
produce a non-functional "effect"
(such as IO). More on that later.

-/

inductive unit : Type
| star

end hidden