namespace hidden


universe u

/-
Version 1
-/

structure has_mul'' (α : Type u): Type (u+1) := 
(mul : α → α → α)

-- def has_mul''_bool_type := has_mul'' bool 

def has_mul''_bool : has_mul'' bool := has_mul''.mk band -- in bool lib
def has_mul''_nat : has_mul'' nat := has_mul''.mk nat.mul -- in nat lib

/- Later on -/

axioms (b1 b2 : bool)
#check has_mul''_bool.mul 

def n1 := 3
def n2 := 4

#eval has_mul''_nat.mul n1 n2

/-
Version 2
-/

structure has_mul' {α : Type u}: Type (u+1) := 
(mul : α → α → α)

-- def has_mul''_bool_type := has_mul'' bool 

def has_mul'_bool : has_mul' := has_mul'.mk band -- in bool lib
def has_mul'_nat : has_mul' := has_mul'.mk nat.mul -- in nat lib

/- Later on -/

#check has_mul'_bool.mul 
#eval has_mul'_nat.mul n1 n2

def my_fancy_mul' : nat → nat → nat 
| n1 n2 := has_mul'_nat.mul n1 n2

#eval my_fancy_mul' 3 4

/-
Final version. Typeclasses in Lean.
-/
@[class]  
structure has_mul (α : Type u): Type u := 
(mul : α → α → α)

instance has_mul_bool : hidden.has_mul bool := has_mul.mk band -- in bool lib
instance has_mul_nat : hidden.has_mul nat := has_mul.mk nat.mul -- in nat lib

/-
When I create typeclass instances, they get stored in a database
and the typeclass inference mechanism can find these instances by
type. 
-/

/-
Implicit instance arguments
-/

--def my_fancy_mul (α : Type) [tc : has_mul α] : α → α → α := tc.mul
def my_fancy_mul {α : Type} [tc : has_mul α] : α → α → α := tc.mul

-- #eval (my_fancy_mul nat) 3 4
-- #eval (my_fancy_mul bool) tt ff

#eval my_fancy_mul 3 4
#eval my_fancy_mul tt ff
#eval my_fancy_mul "Hello" "Lean" -- there's no instance for the string type!

/-
Ad hoc polymorphism. Operator overloading.
-/

/-
Syntactic alternative:
class has_mul (α : Type u) := (mul : α → α → α)
-/

end hidden
