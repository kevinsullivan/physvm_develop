import .aff1Kcoord_std
import data.real.basic

/-
Make a frame from points and vectors in 
std_space, then induce a new coordinate
space, space2, around it.
-/

axioms p1 p2 : point (std_space ℝ 0)
#check 3 • (p2 -ᵥ p1)
#check 3 • (p2 -ᵥ p1) +ᵥ p2

#check p1

noncomputable def p_1 : point (std_space ℝ 0) := mk_point (std_space ℝ 0) 1 
noncomputable def p_2 : point (std_space ℝ 0) := mk_point (std_space ℝ 0) 2 
noncomputable def v_2 : vectr (std_space ℝ 0) := mk_vectr (std_space ℝ 0) 2

#check p_1
#check v_2
#check p_2 -ᵥ p_1
#check (p_2 -ᵥ p_1) +ᵥ p_2
#check v_2 +ᵥ p_2


def s_2 : ℝ := 2  -- add 1 1 in field K
noncomputable def fr_1 : fm ℝ 0 := mk_frame p_2 v_2  
noncomputable def space2 := mk_space ℝ fr_1 


/-
Make a frame from points and vectors in 
space2, then induce a new coordinate
space, space3, around it.
-/
noncomputable def p_3 := mk_point space2 3    -- at 8?
noncomputable def p_3' := mk_point space2 3    -- at 8?
noncomputable def v_3 : vectr space2 := mk_vectr space2 3    -- 3x
noncomputable def fr_2 : fm ℝ 0 := mk_frame p_3 v_3
noncomputable def space3 := mk_space ℝ fr_2

/-
Vector space operations
-/
noncomputable def v_v_add : vectr (std_space ℝ 0) := v_2 + v_2
noncomputable def v_sub : vectr (std_space ℝ 0) := v_2 - v_2
noncomputable def v_neg : vectr (std_space ℝ 0) := -v_2
noncomputable def v_smul : vectr (std_space ℝ 0) := 3 • v_2

/-
Affine operations
-/
noncomputable def v_p_add : point (std_space ℝ 0) := v_2 +ᵥ p_2
noncomputable def p_p_sub : vectr (std_space ℝ 0) := p_2 -ᵥ p_2

/-
Operations down in pt/vec
-/
noncomputable def pt1 := p_1.to_pt
noncomputable def pt2 := p_2.to_pt
noncomputable def pt3 := pt2 -ᵥ pt1

/-
-/
noncomputable def fr_1' : fm ℝ 1 := mk_frame p_2 v_2        -- error 
noncomputable def space2' := mk_space ℝ fr_1'
noncomputable def v_3' : vectr space2' := mk_vectr space2' 3

/-
TODO: Add examples of definitions and
applications of transformations between
coordinate systems. 
-/