namespace hidden

/-
The polymorphic type, prod α β, is 
the type whose values are ordered
pairs the first elements of which 
are of type α and the second elements
of which are of type β.
-/

universe u

structure prod (α β : Type u) : Type u :=
(fst : α) (snd : β)

/-
The names of the fields, fst and snd,
are also used to generated projection
functions for the corresponding fields.
-/

end hidden