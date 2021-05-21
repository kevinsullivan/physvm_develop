import linear_algebra.affine_space.affine_equiv

universes u

variables (K : Type u) [field K] [inhabited K] (pt vec : Type u → Type u)

open_locale affine

instance t : add_comm_group (vec K) := sorry
instance t2 : affine_space (vec K) (pt K) := sorry
instance t3 : module K (vec K) := sorry

#check  (pt K) ≃ᵃ[K] (pt K)
