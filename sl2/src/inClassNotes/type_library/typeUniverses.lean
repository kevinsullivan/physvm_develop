/-
Lean's type hierarchy
-/

namespace hidden1

universe u

structure box (α : Type u) : Type u :=
(val : α)

def b3 : box nat := box.mk 3

def nope : box Type := box.mk nat

/-
Every term has a type. 
Types are terms, too.

The type of 3 is ℕ.
ℕ is a type, so it has a type.
The type of ℕ (#check) is Type.

So here's a picture so far.

     Type (aka Type 0)        
      /  |  \ ..... \
  bool  nat string (box nat) ...
  / \    |    |        |  
  tt ff  3   "Hi!" (box.mk 3)

We can pass 3 to box'.mk because
its type, nat, "belongs to" Type.

Can we pass nat to box'.mk?
-/

def bn := box.mk nat    -- No!

/-
A picture tells us what went wrong.

         ???
          |
        Type 0        (α := Type : ???)
        /  |  \
    bool nat string   (a := nat : Type)
    / \   |    |
    tt ff  3   "Hi!"  

Above Type 0 is an infinite stack of 
higher type universes, Type 1, Type 2,
etc. 
-/

#check Type 0
#check Type 1
#check Type 2
-- etc

/-
In the earlier example, we declared
the type of α to be Type, but if we
bind a := (nat : Type), the Lean will
infer that α := (Type : Type 1). So 
we get a type error.

Now if we change the type of α from
Type to Type 1, we'll have a different
problem. THINK TIME: What is it?
-/



end hidden1

/-
The solution is to make our box
type builder generic with respect
to the "type universe" in which
α lives. We do this by declaring
an identifier to be a universe
variable, and then add it after
"Type" in our type declaration.
-/

universe u

structure box (α : Type u) : Type u :=
(val : α)

def b3 : box nat := box.mk 3 
def bt : box Type := box.mk nat 

/-
Think time: What are the types of b3,
box nat, bt, and box Type?
-/

#check b3
#check box nat
#check bt
#check box Type


-- Yay!

/-
Why so complex? To avoids logical inconsistency.

Russell's Paradox.

Consider the set, S, of all sets that do not 
contain themselves. Does S contain itself? 

If the answer is yes, then the answer must
be no, and if it's no, it must be yes, so 
there is a contradiction in either case. A
logic in which it's possible to derive a 
contradiction is of no use at all because
in such a logic true = false so anything
that can be proved to be true can also be
proved to be false, and vice versa.

Suppose doesn't contain itself. Well, then
it must be in S because S is the set of all
such sets.#check

Now suppose it does contain itself then it
must not contain itself, because contains
only sets that don't contain themselves. 

This insight evolved out of work to place
all of mathematics on a logical foundation.
The attempt to place it on a foundation of
naive set theory failed. This failure led
to changes in set theory and also to the
emergence of an early form of set theory.
The key idea there was to rule out the 
very idea of a set that contains itself,
as being non-sense. What you see in Lean's
type system is a modern instantiation of
the idea of stratified type universes in
which no type can have itself as a value.
-/

