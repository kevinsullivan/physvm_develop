import algebra.module.basic
import linear_algebra.affine_space.affine_equiv
import algebra.direct_sum
import linear_algebra.direct_sum_module
import tactic.linarith
import .lin2kcoord

open_locale direct_sum

universes u 




variables (K : Type u) [field K] [inhabited K] (n : ℕ) (ng1 : n > 1)

/-
In mathematics, a space is a **set**  with some added structure.
-/
abbreviation lin2k_sum := ⨁(i : fin (n)), (λi, K × K) i

instance : module K (lin2k_sum K n) := by apply_instance

def mk_finset (n : ℕ) : finset (fin n) := sorry

def finsetn := mk_finset n

def mk_linnk : (fin (n) → K × K) → lin2k_sum K n :=
  λv, 
  let val : Π (i : (↑(finsetn (n)) : set (fin (n)))), (λi, K × K) i.val := λi, v i in
  direct_sum.lmk K _ _ _ (val)

def mk_linnk' : (fin (n) → K × K) → lin2k_sum K n :=
  λv, 
  let val : Π (i : (↑(finsetn (n)) : set (fin (n)))), (λi, K × K) i.val := λi, v i in
  direct_sum.lmk K _ _ _ (val)