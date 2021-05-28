import data.real.basic
import .aff1K


-- Operations on vectors using vec type
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
noncomputable def p4c : ℝ := pt_coord ℝ p4


