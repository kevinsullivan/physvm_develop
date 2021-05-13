import .aff1Kcoord_std
import data.real.basic

/-
Make a frame from points and vectors in 
std_space, then induce a new coordinate
space, space2, around it.
ℚ 
-/

def p_1 : point (std_space ℚ 0) := mk_point (std_space ℚ 0) 1 
def v_1 : vectr (std_space ℚ 0) := mk_vectr (std_space ℚ 0) 2


def p_2 : point (std_space ℚ 0) := mk_point (std_space ℚ 0) 5 
def v_2 : vectr (std_space ℚ 0) := mk_vectr (std_space ℚ 0) 7

 def fr_1 : fm ℚ 0 := mk_frame p_2 v_2  
 def space2 := mk_space ℚ fr_1 
 def p_3 := mk_point space2 1    -- at 8?
 def p_3' := mk_point space2 3    -- at 8?
 def v_3 : vectr space2 := mk_vectr space2 2    -- 3x
 def fr_2 : fm ℚ 0 := mk_frame p_3 v_3
 def space3 := mk_space ℚ fr_2

/-
-/
 def fr_1' : fm ℚ 0 := mk_frame p_2 v_1        -- expect error 
 def space2' := mk_space ℚ fr_1'


def mytr := space2.fm_tr space2'
def mytr2 := space2.fm_tr (std_space ℚ 0)


def ltr : point space2 → ℚ × ℚ    :=
  λp, (1, 
                        p.to_prod.2*v_2.to_prod.2 + p_2.to_prod.2)

#eval v_2.to_prod
#eval p_2.to_prod

def vtr : vectr space2 → ℚ × ℚ    :=
  λp, (0, 
                        p.to_prod.2*v_2.to_prod.2 + p_2.to_prod.2)

#eval p_3.to_pt.to_prod
#eval v_3.to_vec.to_prod
#eval (mytr2.transform_vectr v_3).to_vec.to_prod
#eval (mytr2.transform_point p_3).to_pt.to_prod
#eval vtr v_3
#eval ltr p_3



def vtr2 : ℚ × ℚ → ℚ × ℚ    :=
  λp, (0, 
                        (p.2 - p_2.to_prod.2)/v_2.to_prod.2)

#eval vtr2 (vtr v_3)
/-
TODO: Add examples of definitions and
applications of transformations between
coordinate systems. 
-/