import ...inClassNotes.typeclasses.monoid.monoid

/-
Create a file, typeclasses.lean, to hold
all of the code for this assignment. Copy
definitions from files given in class when
you need to incorporate those definition in
this file. Use namespaces to avoid naming
conflicts if/as necessary.
-/

/- 
1. Define and use an add_monoid typeclass

We've defined monoid as a typeclass of
*multiplicative* monoids. Each instance
carries (1) a multiplicaton operator for
a given type of argument, (2) an identity
element for that operator, (3) data that
certify that the multiplication operator
is associative, (4) and data that certify
that the identity element really is both
a left and a right identity.

Your task here is to define a typeclass,
add_monoid, for what we'll call additive
monoids. An instance of this typeclass,
for a given type, will carry (1) an add
function for objects of that type, (2) a
zero element for that type, (3) data that 
show that the given addition operator is 
associative, (4) data that show that the
zero object really is a left and right
identity for the addition operator.

To this end, following the pattern that 
we've already established: define several
typeclasses as follows. Use a namespace 
(e.g., hidden) to avoid clashing with any
typeclass names already defined by Lean.

has_add α     -- addition function for α 
has_zero α    -- identity for add for α 
add_semigroup α -- add must be associative
add_monoid α extends add_semigroup α, has_zero α

Next use these typeclasses to define 
instances that provide additive monoid
structures for the types nat, string, 
and bool. Define the overloaded add for 
nat to be nat.add; for string, append; 
and for bool, bor.
-/


/-
2. Define a robust additive foldr function.

Define a version of our simple list fold 
function, called add_foldr, that (for any type, 
α), instead of taking an identity value (a : α), 
a binary function,  (f : α → α → α), and a list, 
(l : list α), now takes (implicitly) an additive
monoid instance, (i : add_monoid α), and a list, 
(l : list α), and that then uses the identity 
element and binary function provided by i to 
implement foldr.

Why? Because now the identity and the function
can't get out of synch, and you can also be
sure that the identity element value really is
an identity for the given function and type α!

Show that you can apply your now *overloaded*
fold function to lists of values of type nat,
bool, and string, and that the right results
are produced in each of these cases.
-/

/-
3. Define a version of our simple list fold 
function, called mul_foldr, that (for any type, 
α), instead of taking an identity value (a : α), 
a binary function,  (f : α → α → α), and a list, 
(l : list α), now takes a multiplicative monoid 
instance, (i : monoid α), and a list,  
(l : list α), and that then uses the identity 
element and binary function provided by i to 
implement the fold.

Show that you can apply your now *overloaded*
fold function to lists of values of type nat
and bool (we won't have an implementation of
mul for strings), and that the right results
are produced in each of these cases.
-/


/-
4. Required for graduate students, 
extra credit for undergraduates. Lean
provides the following typeclass, called
functor. 

class functor (f : Type → Type) : Type  :=
(map : Π {α β : Type u}, (α → β) → f α → f β)
-/

/-
Crucial idea: polymorphic types, such as list
and option, are of type, Type → Type. What we
define here is a typeclass for such a polymorphic
type. So reasonable values for f, here, are things
like list and option!
-/


-- Haskell functor typeclass, here called has_map
-- Todo: Fix this. No higher type universes
class has_map (context : Type  → Type) : Type 1 :=
(fmap : Π {α β : Type}, (α → β) → context α → context β)

-- implementation for list α 
def list_map {α β : Type} : (α → β) → list α → list β 
| f list.nil := []
| f (h::t) := f h::list_map f t

-- implementation for option α 
def option_map {α β : Type} : (α → β) → option α → option β 
| f none := none
| f (some a) := some (f a) 

-- instance for list
instance list_has_map : has_map list := 
⟨ @list_map ⟩

-- instance for option
instance option_has_map : has_map option :=
⟨ @option_map ⟩ 

-- overloaded map operator
def map' 
( context : Type → Type ) -- is list, option, box...
[m : has_map context]     -- map function for it
--{ α β : Type} 
--(f : α → β) 
--(c : context α) 
-- : context β 
:= (m.fmap) 

#check (map' list) 
#eval   map' list nat.succ [1,2,3]
--(c β)        ctxt  f:α → β (c α)   


-- overloaded map operator, implicit context argument
def map 
{ context : Type → Type } -- is list, option, box...
[m : has_map context]     -- map function for it
--{ α β : Type} 
--(f : α → β) 
--(c : context α) 
-- : context β 
:= (m.fmap) 

  #eval map nat.succ [1,2,3]
  #eval map string.length ["Hello", "There!"]
  #eval map (λ (n : nat), if (n>0) then tt else ff) [5,4,0,7,8,4,0,8]


/-
FOLDR
-/


universes u₁ u₂ u₃ 

def mk_reducer 
{α : Type u₁} 
{β : Type u₂} 
{φ : Type u₃} :
(α → φ) → (φ → β → β) → (α → β → β)
| conv comb :=  comb ∘ conv 

def foldrx 
  {α : Type u₁} 
  {β : Type u₂} 
  {φ : Type u₃} :
  β → (α → φ) → (φ → β → β) → list α → β
| i v b [] := i
| i v b (h::t) := (b ∘ v) h (foldrx i v b t)  -- haha


def foldr 
  {α : Type u₁} 
  {β : Type u₂} 
  {φ : Type u₃} :
  β → (α → β → β) → list α → β
| id op [] := id
| id op (h::t) := op h (foldr id op t)




-- NB above: import ...inClassNotes.typeclasses.monoid.monoid

/-

-- has_mul: a type with a binary mul operator, (mul : α → α → α)
@[class]  
structure has_mul (α : Type u): Type (u+1) := 
(mul : α → α → α)

-- semigroup: a type with a binary mul operator that's associative
@[class]
structure semigroup (α : Type u) extends has_mul α : Type u :=
(mul : nat)
(mul_assoc : ∀ (a b c_1 : α), mul (mul a b) c_1 = mul a (mul b c_1))

@[class]
structure has_monoid (α : Type u) extends (semigroup α), (has_one α) : Type u 
-/

def add_foldr 
  {α : Type u₁} : hidden.has_one α → hidden.has_mul α → 
  list α → α  
| o m [] := o.one
| o m (h::t) := m.mul _ _

/-
https://www.youtube.com/watch?v=mvmuCPvRoWQ
-/

