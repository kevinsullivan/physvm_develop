/-
Lean provides the following functor typeclass. 

class functor (c : Type u → Type v) : Type  :=
(map : Π {α β : Type u}, (α → β) → c α → c β)

Key observation: polymorphic type builders, such 
as list α and option α, are of type, Type → Type. 
-/

#check @list
#check @option

/-
So reasonable values for (c : Type → Type) here
are values such as list, box, and option. It can
be useful to think of such arguments as "container"
types, or more generally as types that surround
values of other types with some kind of "context."
-/

/-
Second key observation: the functor typeclass
extends our interface to list, option, and other
such types to include a new mapping operator, map.
-/

/-
Consider our list, option, and box types as types
that augment values with surrounding context. 
For example, the nat, 3, can be put in a list 
context as [3], in an option context as (some 3), 
or in a box context as (box.mk 3).
-/
universes u v

structure box (α : Type u) : Type u :=
mk :: (val : α)

/-
We've already seen that we can define higher
order functions that can *map* other function over
such "containers". For example, given a function
of type ℕ → bool, we can map it over a list of ℕ 
values to get a corresponding list of bool values,
over an option ℕ, or over a box ℕ. In each case,
we transform the value in the context without
changing the structure of the context. So, for
example, mapping over a list always returns a
list of the same shape (length).
-/

def box_map   {α β : Type u} : 
  (α → β) → box α → box β 
| f (box.mk a) := box.mk (f a) 

def list_map  {α β : Type u} : 
  (α → β) → list α → list β 
| f list.nil := []
| f (h::t) := f h::list_map f t

def option_map {α β : Type u} :
  (α → β) → option α → option β 
| f none := none
| f (some a) := some (f a) 

/-
Now comes a key insight: we can characterize *fmap* 
as an overloaded operator, that takes a function and 
*some kind of* container (list, box, option, etc.),
and that then maps that function over the contents of 
the container to produce a new container of exactly 
the same "shape" as the original (e.g., a list of the
same length), with values derived by applying f to
the values in the original "context/container". We 
can now really make sense of the type of any such 
overloaded "map" function:

(fmap : Π {α β : Type u}, (α → β) → c α → c β)

Given types α and β, a function, f : α → β, and
a "container/context", (c α) -- such as list α 
or option α -- map will return a "context", of 
type (c β): the same kind of container, and one
of the same shape, but now containing a value
or a set of values as transformed by f.
-/

/-
As we see above, we can define implementations
of such a map function for completely different
types of context/container objects: lists, boxes,
options, etc. We can abstract this collection of
types (or here, polymorphic type builders) as a
typeclass. One name we might give it is has_map.
So a type builder such as list would be "in" this
typeclass if it provided an instance of has_map,
and that instance would hold the implementation
of map for lists, namely list_map.
-/

/-
  has_map typeclass
-/

class has_map (c : Type u → Type v) : Type (max (u+1) v) :=
(map : Π {α β : Type u}, (α → β) → c α → c β)

/-
  instances for box, list, option
-/

#check list_map
#check @list_map

instance list_has_map   : has_map list    := ⟨ @list_map ⟩
instance option_has_map : has_map option  := ⟨ @option_map ⟩ 
instance box_has_map    : has_map box     := ⟨ @box_map ⟩ 

/-
In practice, the name "functor" is typically used
for this typeclass. We can use Lean's definition
of this typeclass. That said Lean's definition of
functor requires an implementation of a second
function, which we'll just ignore here. 
-/

#print functor

instance option_as_function : functor option := ⟨ @option_map, sorry⟩ 
instance list_as_functor    : functor list   := ⟨ @list_map, sorry ⟩
instance box_as_functor     : functor box    := ⟨ @box_map, sorry ⟩ 



/-
We can now define an overloaded map operator, usually
called fmap.
-/

-- first version 
def fmap'
( c : Type → Type )   
[functor c] 
{ α β : Type} 
(f : α → β) 
(l : c α) := functor.map f l


#check @fmap' list
#check @fmap' box
#check @fmap' option

#eval fmap' list nat.succ [1,2,3]
#eval fmap' option nat.succ (some 1)
#reduce fmap' box nat.succ (box.mk 3)


-- final version
open functor
def fmap
{ c : Type → Type }  
[functor c] 
{ α β : Type} 
(f : α → β) 
(l : c α) := map f l

-- map over list
#reduce fmap nat.succ [1,2,3,4,5]
#reduce fmap nat.succ (some 1)
#reduce fmap nat.succ (box.mk 3)
#reduce fmap (λ n, n * n) [1,2,3,4,5]
#reduce fmap (λ (s : string), s.length) ["Hello", "there", "how", "are", "you?"]

/-
So functor is a typeclass. You can
think of it as an kind of abstract
interface that can be used to extend 
the native interface of a type and 
its associated functions. To extend
the interface of a particular type, 
you define a new instance. It defines
how each element of the abstract
interface is implemented for that
type. Here, the instances define how
the new abstract "map" function is
impleented for each of the list,
box, and option types. 

We can apply all of this machinery in 
several ways. One is to define overloaded
operators. Here we define fmap as an
overloaded map function. Given a type
for which there is a typeclass, it finds
the relevant instance, grabs the value
in its map field, and uses it.
-/

/-
From here, you'll want to learn about
the typeclasses called applicative and
monad. Each one just defines abstract
interfaces than can be implemented for
various polymorphic type builders. 

As an example, you might define a general
interface for applying a function *that
is itself in a context* to a value that
is in the same kind of context to get a 
result also in that context. To be more
concrete, suppose you have a value of 
type (option α → β) and a value of type
(option α). You can surely now come up
with a way to "apply" the former to the 
latter to get a value of type option β. 
Now do the same thing for list and box.
Now generalize from option and box to 
any kind of "container/context" type,
and, voila, you have an interesting new
typeclass, and what you need to create
a instances for various container types. 

If this were a class just in functional
programming, we'd go ahead and continue 
in this vein to cover the important monad
typeclass, which has diverse applications
involving compositions of operations and
encapsulation of results produced by non
purely functional means (e.g., I/O), so
that non-functional "effects" can be
safely integrated with functional code.

I recommend that you now go read the
typeclass chapters in Learn You a Haskell,
if you're intersted. Rather, we now turn
to another use of typeclasses, and that
is to formalize abstract interfaces in
mathematics. E.g., the concept of a group
is really an interface concept! Something
is a group if it *implements* the group
"interface", which requires (1) a set of
objects, (2) a binary operator, (3) an
identity element, and (4) evidence that 
rules for being a group are followed. 
Many, many different structures can
implement this interface. We'll now look
at one, the Dihedral group on a square. 

This work, in turn, will set us up to 
make the transition to mathematial logic
and proof construction -- because the
kind of evidence we'll seek will come
exactly in the form of *proofs* that 
specified rules are followed.
-/
