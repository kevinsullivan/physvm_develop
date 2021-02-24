import data.real.basic
import linear_algebra.affine_space.basic
import linear_algebra.basis
open_locale affine

universes u v w

/-
A version of the unit type that can
live in any type universe. Adds type
universe parameter to usual unit type.
-/

inductive uunit : Type u
| star


structure affine_space_type
    --(id : ℕ)
    (K : Type u)
    (X : Type v)
    (V : Type w)
    [ring K] 
    [add_comm_group V] 
    [module K V]  
    [affine_space V X]

def tuple {K : Type} : nat → Type u
| 0 := uunit
| (n' + 1) := K × (tuple n')

variables 
{K : Type} [ring K] [inhabited K] 
{α : Type v} [has_add α]
(n : ℕ)   -- TODO: change this name from n to dim
-- (a b : α) (al bl : list α)
-- (x y : K) (xl yl : list K)

def tuple_add : Π {n : nat}, @tuple K n → @tuple K n → @tuple K n
| 0 t1 t2 := uunit.star
| (n' + 1) (h, t) (h', t') := (h + h', tuple_add t t')

def tuple_scalar_mul : Π {n : nat}, K → @tuple K n → @tuple K n
| 0 _ _ := uunit.star
| (n' + 1) k (h,t) := (h*k, tuple_scalar_mul k t)

def zerotuple : Π (n : nat), @tuple K n
| 0 := uunit.star
| (n' + 1) := (0, zerotuple n')

def head : Π {n : nat}, (n > 0) → @tuple K n → K
| 0 _ _ := 0  -- can't happen
| (n' + 1) _ (h,t) := h

@[ext]
structure aff_vec_coord_tuple :=
(t : @tuple K (n+1))
(inv : head (by sorry) t = 0)

@[ext]
structure aff_pt_coord_tuple :=
(t : @tuple K (n+1))
(inv : head (by sorry) t = 1)

variables 
(x y : @aff_vec_coord_tuple K _ _ n)
(a b : @aff_pt_coord_tuple K _ _ n)


/-
Now what we need to prove at the end 
of the day is that for a given K and n,
our vector and point coordinate tuples
for an affine space, which is to say
that they constitute an "aff_torsor K n."

My approach at this point would be to
work backwards from this goal, copied
in just below this comment, brining in
and adapting the relevant parts of the 
affine_coordinate_space.lean file, as
needed (recursively).
-/



instance aff_coord_is : 
    affine_space 
        (@aff_vec_coord_tuple K _ _ n) 
        (@aff_pt_coord_tuple K _ _ n) := 
    aff_torsor K n