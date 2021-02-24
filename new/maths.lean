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

variables 
(K : Type) [ring K] [inhabited K] 
{α : Type v} [has_add α]
-- (n : ℕ) -- no longer assume fix n in this file
-- (a b : α) (al bl : list α)
-- (x y : K) (xl yl : list K)

def tuple : nat → Type u
| 0 := uunit
| (n' + 1) := K × (tuple n')

/-
Note: The tuple type builder takes the following
arguments
K             -- explicit
[ring K]      -- implicit
[inhabited K] -- implicit
n             -- explicit
-/
#check @tuple

def tuple_add : 
  Π {n : nat}, tuple K n → tuple K n → tuple K n
| 0 t1 t2 := uunit.star
| (n' + 1) (h, t) (h', t') := (h + h', tuple_add t t')

def tuple_scalar_mul : Π {n : nat}, K → tuple K n → tuple K n
| 0 _ _ := uunit.star
| (n' + 1) k (h,t) := (h*k, tuple_scalar_mul k t)

def zero_tuple : Π (n : nat), @tuple K _ _ n
| 0 := uunit.star
| (n' + 1) := (0, zero_tuple n')

def head : Π {n : nat}, (n > 0) → tuple K n → K
| 0 _ _ := 0  -- can't happen
| (n' + 1) _ (h,t) := h

#check @head 

@[ext]
structure aff_vec_coord_tuple (n : nat) :=
(tup : tuple K (n+1))
(inv : head K (by sorry) tup = 0)

@[ext]
structure aff_pt_coord_tuple  (n : nat) :=
(tup : tuple K (n+1))
(inv : head K (by sorry) tup = 1)


def aff_vec_zero_tuple (n : nat) : aff_vec_coord_tuple K n :=
⟨ @zero_tuple K _ _ (n+1), sorry⟩ 

def aff_pt_zero_tuple (n : nat) : aff_pt_coord_tuple K n:=
⟨ (1, @zero_tuple K _ _ n), sorry ⟩ 


/-
variables 
(x y : @aff_vec_coord_tuple K _ _ n)
(a b : @aff_pt_coord_tuple K _ _ n)
-/

/-
Now what we need to prove at the end 
of the day is that for a given K and n,
our vector and point coordinate tuples
form an affine space, which is to say
that they form an "aff_torsor K n." I
think we can prove this for all n by
induction (which is not what's done
in our current "production" version.)
-/

/-
Vectors add on points by displacing them.
-/
def aff_group_action { n : nat } : 
  @aff_vec_coord_tuple K _ _ n → 
  @aff_pt_coord_tuple K _ _ n → 
  @aff_pt_coord_tuple K _ _ n :=
λ vec pt, 
  aff_pt_coord_tuple.mk 
    (tuple_add K vec.tup pt.tup)
    sorry

def aff_group_sub { n : nat } : 
  @aff_pt_coord_tuple K _ _ n → 
  @aff_pt_coord_tuple K _ _ n → 
  @aff_vec_coord_tuple K _ _ n :=
sorry
--    λ x y, ⟨ladd x.1 (vecl_neg y.1), sub_len_fixed K n x y, sub_fst_fixed K n x y⟩

instance (n : nat) : 
  has_vadd (@aff_vec_coord_tuple K _ _ n) (@aff_pt_coord_tuple K _ _ n) :=
⟨ @aff_group_action K _ _ n ⟩ 

instance (n : nat) : 
  has_vsub (@aff_vec_coord_tuple K _ _ n) (@aff_pt_coord_tuple K _ _ n) := 
⟨@aff_group_sub K _ _ n⟩


lemma aff_zero_sadd { n : nat } : 
  ∀ x : @aff_pt_coord_tuple K _ _ n, 
    (@aff_vec_zero_tuple K _ _ n) +ᵥ x = x := sorry

-- still need aff_zero_sadd, aff_add_sadd, aff_vsub_vadd, aff_vadd_vsub

instance aff_torsor (n : nat): 
  add_torsor 
    (@aff_vec_coord_tuple K _ _ n) 
    (@aff_pt_coord_tuple K _ _ n) := 
⟨
  aff_group_action, 
  aff_zero_sadd K n,
  aff_add_sadd K n,
  aff_group_sub,
  aff_vsub_vadd K n, 
  aff_vadd_vsub K n
⟩


instance aff_coord_is (n : nat) : 
      affine_space 
          (@aff_vec_coord_tuple K _ _ n) 
          (@aff_pt_coord_tuple K _ _ n) := 
      aff_torsor K n