import linear_algebra.affine_space.basic
import .uunit 
open_locale affine

universes u v w

variables 
(K : Type u) [ring K] [inhabited K] 
{α : Type v} [has_add α]




/- 
      N-DIMENSIONAL K-TUPLES
-/

def tuple : nat → Type u
| 0 := uunit
| (n' + 1) := K × (tuple n')

/-
Note: tuple takes the following arguments:
K             -- explicit
[ring K]      -- implicit
[inhabited K] -- implicit
n             -- explicit
-/
#check @tuple

-- OPERATIONS

def tuple_add : 
  Π {n : nat}, tuple K n → tuple K n → tuple K n
| 0 t1 t2 := uunit.star
| (n' + 1) (h, t) (h', t') := (h + h', tuple_add t t')

def tuple_scalar_mul : Π {n : nat}, K → tuple K n → tuple K n
| 0 _ _ := uunit.star
| (n' + 1) k (h,t) := (h*k, tuple_scalar_mul k t)

def tuple_negate : Π {n : nat}, tuple K n → tuple K n
| _ t := tuple_scalar_mul K (-1:K) t

def tuple_zero : Π (n : nat), @tuple K _ _ n
| 0 := uunit.star
| (n' + 1) := (0, tuple_zero n')

def tuple_head : Π {n : nat}, (n > 0) → tuple K n → K
| 0 _ _ := 0  -- can't happen
| (n' + 1) _ (h,t) := h

def tuple_tail : Π {n : nat}, (n > 0) → tuple K n → tuple K (n-1)
| 0 _ _ := uunit.star  -- can't happen
| (n' + 1) _ (h,t) := t


-- PROPERTIES

lemma tuple_heads_add_to_head : ∀ (h k : K) (n : nat) (t1 t2 : tuple K n) (gtz : n > 0),
  tuple_head K gtz t1 = h → 
  tuple_head K gtz t2 = k → 
  tuple_head K gtz (tuple_add K t1 t2) = (h + k) :=
begin
  intros h k n t1 t2 gtz t1h t2k,
  cases n,
  cases gtz,
  cases t1 with t1h t1t,
  cases t2 with t2h t2t,
  simp [tuple_head] at t1h,
  simp [tuple_head] at t2k,
  rw t1h,
  rw t2k,
  simp [tuple_add],
  simp [tuple_head],
end

lemma tuple_zero_heads_add_to_zero_head : ∀ (n : nat) (t1 t2 : tuple K n) (gtz : n > 0),
  tuple_head K gtz t1 = 0 → 
  tuple_head K gtz t2 = 0 → 
  tuple_head K gtz (tuple_add K t1 t2) = 0 + 0 :=
begin
apply tuple_heads_add_to_head K 0 0,
end


