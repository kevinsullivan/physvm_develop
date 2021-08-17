import data.real.basic
import .aff1K

universes u 
variables 
(K : Type u) 
[field K]
[inhabited K]

-- direct sum example
variable (n : ℕ )
open_locale direct_sum  -- notation
#check  ⨁(i : fin n), (λi, vec K) i

-- affine equivalence of affine spaces
#check (pt K) ≃ᵃ[K] (pt K) --works!


-- Operations on vectors using vec type
-- Field is ℝ, which is non-computable, so ...
noncomputable def v1 : vec ℝ := mk_vec ℝ 0
noncomputable def v2 : vec ℝ := mk_vec ℝ 3
noncomputable def v3 := v1 + v2
noncomputable def v4 := (2 : ℝ) • v3

-- Operations involving points using pt type 
noncomputable def p1 : pt ℝ := mk_pt ℝ 0
noncomputable def p2 : pt ℝ := mk_pt ℝ 3
noncomputable def p3 := p1 -ᵥ p2
noncomputable def p4 := v4 +ᵥ p2

-- get coordinate of pt
noncomputable def p4c : ℝ := pt.coord p4


