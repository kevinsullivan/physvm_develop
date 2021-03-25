import .affine1K_standard

universes u
variables 
{K : Type u} [field K] [inhabited K] 
{α : Type u} [has_add α]

/-
Make a frame from points and vectors in 
std_space, then induce a new coordinate
space, space2, around it.
-/

axioms p1 p2 : point K (std_space K)
#check 3 • (p2 -ᵥ p1)
#check 3 • (p2 -ᵥ p1) +ᵥ p2

def p_1 : point K (std_space K) := mk_point K (std_space K) (1:K) 
def p_2 : point K (std_space K) := mk_point K (std_space K) (2:K) 
def v_2 : vectr K (std_space K) := mk_vectr K (std_space K) (2:K)

#check p_2 -ᵥ p_1
#check (p_2 -ᵥ p_1) +ᵥ p_2
#check v_2 +ᵥ p_2
#reduce p_2 -ᵥ p_1


def s_2 : K := 2  -- add 1 1 in field K
def fr_1 : fm K := mk_frame K p_2 v_2  
def space2 := mk_space K (@fr_1 K _ _) 

/-
Make a frame from points and vectors in 
space2, then induce a new coordinate
space, space3, around it.
-/
def p_3 := mk_point K space2 (3:K)    -- at 8?
def v_3 : vectr K space2 := mk_vectr K space2 (3:K)    -- 3x
def fr_2 : fm K := mk_frame K p_3 v_3
def space3 := mk_space K (@fr_2 K _ _)

/-
Vector space operations
-/
def v_v_add : vectr K (std_space K) := v_2 + v_2
def v_sub : vectr K (std_space K) := v_2 - v_2
def v_neg : vectr K (std_space K) := -v_2
def v_smul : vectr K (std_space K) := 3 • v_2

/-
Affine operations
-/

def v_p_add : point K (std_space K) := v_2 +ᵥ p_2
def p_p_sub : vectr K (std_space K) := p_2 -ᵥ p_2