import algebra.module.basic
import linear_algebra.affine_space.affine_equiv
import algebra.direct_sum
import linear_algebra.direct_sum_module
import tactic.linarith
import .lin2kcoord_sum

open_locale direct_sum

universes u 


variables (K : Type u) [field K] [inhabited K] (n : ℕ)

variables 
  (finntoKxK : (fin (n) → K × K))
  (vectorKxKn : (vector (K × K) n))
--abbreviation lin2k_sum := ⨁(i : fin (n)), (λi, K × K) i
#check mk_linnk K n (finntoKxK)
#check mk_linnk' K n (vectorKxKn)

