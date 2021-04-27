/-
In this file, I explain why the foldr function has
such a funny-looking type. 


The following examples have much in common

- Reducing a list of strings to a bool that indicates whether all of them have a given property
- Reducing a list of strings to a natural number that indicates the sum of all of their lengths

These are examples of the generalized concept of a right fold. Here are two simpler examples.

- Reduce a list of natural numbers to a natural number, by (1) applying a give binary operator
between the head of the list and the reduction (recursively) of the rest of the list; or in the
case where the list is empty, returning the identity for the given binary reduction operator.
- Reduce list of strings to a single string by "appending them all together", where that means
applying the binary append operation between each pair of elements, inserting the identity at 
the end of the list.

foldr 0 nat.add (5::4::3::2::1::list.nil)

5 + (foldr 4::3::2::1::list.nil)
5 + (4 + (3 + (foldr ::2::1::list.nil)))
5 + (4 + (3 + (2 + (foldr 1::list.nil))))
5 + (4 + (3 + (2 + (1 + (foldr list.nil)))))

foldr 1 nat.mul (5::4::3::2::1::list.nil)

5 * (foldr 4::3::2::1::list.nil)
5 * (4 * (3 * (foldr ::2::1::list.nil)))
5 * (4 * (3 * (2 * (foldr 1::list.nil))))
5 * (4 * (3 * (2 * (1 * (foldr list.nil)))))

-/

def aList := 5::4::3::2::1::list.nil

/-

rfold "" string.append  [ "Hello", ", ", "Lean", "!"] reduces to "Hello, Lean!" Here's how:

- rfold "" (++) [ "Hello", ", ", "Lean", "!"] 
- "Hello" ++ (rfold "" ++ [", ", "Lean", "!"]
- "Hello" ++ (", " ++ (rfold "" ++ ["Lean", "!"])
...
= "Hello" ++ (", " ++ ("Lean" ++ (rfold "" ++ ["!"])))
-/

def fold : nat → (nat → nat → nat) → list nat → nat 
| id f (list.nil) := id
| id f (h::t) := f h (fold id f t)

universe u

def fold' {α : Type u} : α → (α → α → α) → list α → α 
| id f (list.nil) := id
| id f (h::t) := f h (fold' id f t)

#eval fold' 0 (+) aList
#eval fold' 1 (*) aList
#eval fold' tt band [tt,tt,tt,tt,tt]
#eval fold' ff bor [ff]
#eval fold' "" (++) ["Hello, ", "Lean!"]

def ev_str : string → bool := λ s, (s.length % 2 = 0)

#eval ev_str "Hello!"

def sList := ["Hello!, ", "Lean"]

def fold'' tt band sList  -- No

#eval fold'' tt band "Hello"::"Lean"::list.nil -- No

/-
band (ev_str "Hello") (fold'' tt band "Lean"::list.nil)
band ff (band (ev_str "Lean") (fold'' tt band list.nil))
band ff ( band tt tt) 
ff
-/

--def fold'' {α β : Type u} (id : β) (p : α → β) (r : α → β → β) : β :=

def fold'' {α β : Type u} : β → (α → β) → (β → β → β) → list α → β 
| id p r (list.nil) := id
| id p r (h::t) := r (p h) (fold'' id p r t) 

#eval fold'' tt ev_str band sList
 
def s_b_r : string → bool → bool  
| s b := band (ev_str s) b

universes u₁ u₂ u₃
def foldr 
  {α : Type u₁} 
  {β : Type u₃} 
  :
  β →             -- overall answer for list.nil
  (α → β → β) →   -- answer for head and tail reduced        
  (list α → β)    -- returns a list reducer
| b f list.nil := b
| b f (h::t) := f h (foldr b f t)


def blist := [tt, tt, ff, ff, tt, tt, tt, tt, ff]

#eval foldr tt band blist   -- bool → bool → bool
#eval foldr ff bor blist    --   α  →   β  → φ 


-- reduce list of strings to bool indicating whether any string is of even length
-- reduce list of strings to bool indicating whether all strings are of even length

/-
finally this function combines the rest of applying even to the string at the head 
of the list with the reduced value obtained recursively for the rest of the lsit. It
is from here the "rightness" of foldr comes. For empty, return identity. Otherwise
reduce head to a value and combine that value with the fold of the rest of the list.
-/

def all_even : string → bool → bool 
| h r := band (ev_str h) r  -- conjoin answer for head with answer for rest of list

def some_even : string → bool → bool 
| h t := bor (ev_str h) t

#eval foldr tt all_even ["Hello,", "Lean!"]

def mk_reducer
{α : Type u₁} 
{β : Type u₃} :
(α → β) → 
(β → β → β) → 
(α → β → β)
| hr rr := 
λ b, rr (hr b)


#eval foldr tt (mk_reducer ev_str band) ["Hello,", "Lean"]
#eval foldr ff (mk_reducer ev_str bor) ["Hello", "Lean!"]

def has_even_string : list string → bool :=
fun (l : list string), foldr ff (mk_reducer ev_str bor) l

def all_even_string : list string → bool :=
fun (l : list string), foldr tt (mk_reducer ev_str band) l

#eval has_even_string ["Hello,", "Lean!"]
#eval all_even_string ["Hello,", "Lean!"]

def append_all : list string → string :=
fun l, foldr "" (++) l

#eval append_all ["Hello,", "Lean!"]

/-
A PROBLEM REARS
-/

def all_even_string_bad : list string → bool :=
fun (l : list string), foldr ff (mk_reducer ev_str band) l
-- EXERCISE: What's the bug here? There is one.

