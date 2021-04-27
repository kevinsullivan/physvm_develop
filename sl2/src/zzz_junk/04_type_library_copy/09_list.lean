#print nat

namespace hidden

/-
The list α type represents the 
set of lists of values of type
α. So "list nat", for example, is
the type of lists that contain
natural numbers. It explains that 
such a list is either empty (nil) 
or is constructed (cons) from a
single element of type α and a
smaller list (possibly empty) of
the same type. 

This is an inductive definition
in which "larger" objects of a
given type are constructed from
smaller objects of the same type.

The induction starts with the 
base case, nil, representing 
the empty list of values of type
α. A list with one element, h
of type α, is represented as a 
term (cons h nil). And given a
list (t : list α) a list that
comprises a new element (h : α)
followed by the "old" list, t,
represented as (cons h t). We
often refer to the element, h,
first in a list as the "head" of
the list, and the one-smaller
list, t, that follows as the
"tail".

We will interpret these terms
as mathematical sequences of values 
represented by terms of type α. 
-/

universe u

inductive list (α : Type u) : Type u
| nil : list
| cons : α → list → list 

end hidden

