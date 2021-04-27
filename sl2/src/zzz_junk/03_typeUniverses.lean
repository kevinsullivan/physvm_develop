/-
Lean's type hierarchy
-/

namespace hidden1

structure box (α : Type) : Type :=
(val : α)

def b3 : box nat := box.mk 3  

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
Here's the key idea. If a term 
contains, or is parameterized by, 
a value in Type u, where u is any 
natural number, then it must live
(at least) in Type (u+1).


In the our example, (a := nat : Type),
so (α := Type : Type 1)
-/

end hidden1


/-
We've defined our identity functions 
to take (1) any type, α, of type Type,
and (2) any value, a, of the type give 
as the value of α, and to return that 
same value, a. 

Knowing that types are terms, too, 
the clever student will try to apply
our id functions to type-valued terms,
such as nat or bool. Alas, that won't
work. 
-/

#eval id6 nat       -- Nope!

/-
Why? Let's analyze it. That's easier 
if we make the implicit type argument 
explicit using an _. We'll use our id2 
version, which requires that the first, 
type, argument (a value of type, Type)
be given explicitly. Let's start with
an example that works.  
-/

#eval id2 nat 5

/-
Here 3 is value of type nat, and 
nat is a value of type Type. The 
type argument to box has to be a
value of type, Type (a shorthand
for Type 0), so nat will do fine, 
as would bool, string, box nat, etc.

        Type 0 (Type)       
        /  |  \
    bool nat string  (nat : Type) 
    / \   |    |
    tt ff  3   "Hi!"  (3 : nat)

What does the picture look like with a = nat?

          ???
          |
        Type 0        (α := Type : ???)
        /  |  \
    bool nat string  (a := nat : Type)
    / \   |    |
    tt ff  3   "Hi!"  
-/

/-
              ad inf
                |
              Type 2
                |
              Type 1
                |
              Type 0       (α := Type : ???)
             /  |  \
          bool nat string  (a := nat : Type)
          / \   |    |
         tt ff  3   "Hi!"
-/
-- A "sad" solution is to change to (α : Type 1)

def id7 {α : Type 1} (a : α) : α := a


-- Okay, it works when applied to types in Type 0
#reduce id7 nat   -- careful: nat is second argument!
#eval id bool
#eval id string

-- But now it's broken for *values* of these types

#eval id7 nat 5     -- hope for 5

-- And for values in the next "type universe" up

#eval id7 Type      -- hope for Type

/-
Here's the general picture.

               ... ad inf.      -- Type 2 is type of Type 1, etc
                |
             Type 1             -- Type of Type 0
                |
              Type 0            -- Type of usual types
             /  |  \
      ... bool nat string ...   -- usual types
          / \   |    |
         tt ff  5   "Hi!"  ...  -- values of these types
-/ 

/-
Solution is to make definition "polymorphic" in 
type universes.
-/



universe u   -- let u be an arbitrary universe level (0, 1, 2, etc)

-- And let Lean infer u from context

def id {α : Type u} (a : α) : α := a

#reduce id 5      -- 5    belongs to nat,     nat     belongs to Type
#reduce id nat    -- nat  belongs to Type,    Type    belongs to Type 1
#reduce id Type   -- Type belongs to Type 1,  Type 1  belongs to Type 2
#reduce id (Type 10)  -- etc, ad infinitum

-- Yay!

/-
Why such complexity? It avoids certain inconsistencies.

Russell's Paradox.

Consider the set of all sets that do not contain themselves.

Does it contain itself?
If it doesn't contain itself then it must contain itself.
If it does contain itself then it mustn't contain itself.
Either assumption leads to a contradiction, and inconsistency.
Russell introduced stratified types to avoid this problem in set theory.
The hierarchy prevents any type from containing itself as a value.

The very concept of sets containing or not containing themselves
has to be excluded from consideration. Types that contain only 
"lower" types and never themselves solves the problem. Bertrand
Russell is thus a great-great-granddaddy of this aspect of type
theory.

What belongs in higher type universes in practice? It's pretty
straightforward. If an object *contains a value* of type, Type u, 
then that object lives in (at least) Type u+1. Details later on.
-/

/-
This material about type universes is quite abstract, so please
don't worry if it's going over your head at this point. Graduate
students should work hard to grasp it. For the most part I will
avoid defining types in full generality w.r.t. universe levels.
-/

end hidden