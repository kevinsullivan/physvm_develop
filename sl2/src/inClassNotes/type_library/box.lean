namespace hidden

/-
This polymorpmic box type allows 
one to enclose/wrap a value of any
ordinary computational type (of type,
Type) "in" a box structure. Using
"structure" to define this type as
specified here provide a projection
function with the same name, val, as
the field who value it projects
(i.e., accesses and returns).
-/

universe u

structure box (α : Type u) : Type u :=
mk :: (val : α)

def b3 := box.mk 3

#reduce b3

#reduce (box.val b3)
#reduce b3.val


end hidden