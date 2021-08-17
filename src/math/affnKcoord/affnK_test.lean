import data.real.basic
import .affnK

abbreviation K := ℚ 
def dim := 3

def v1 : vec_n K dim := mk_vec_n _ _ ⟨[4,5,6], rfl⟩
#eval v1.coords
def v2 : vec_n K dim := v1 + v1
def v3 := 5•v1 - v2

def p1 : pt_n K dim := mk_pt_n _ _  ⟨[1,2,3], rfl⟩

#eval p1.coords

def p2 : pt_n K dim := v2 +ᵥ p1

#eval p2.coords

def p3 := p1 -ᵥ p2

#eval p3.coords


/-
Code from 6/14 meeting:
-/

/-
Build an n-D affine space from n 1-D spaces
-/
abbreviation affnK (n : nat) := fin n → (affine_space (vec K) (pt K)) 

/-
-/
example : nat := 3

def a1k : affnK ℚ 1 := λ i, by apply_instance
def a2k : affnK ℚ 2 := λ i, by apply_instance
def a3k : affnK ℚ 3 := λ i, by apply_instance

#check a1k
#check a2k
#check a3k


def foo {n1 n2 : nat} (a1 : affnK K n1) (a2 : affnK K n2) : affnK K (n1 + n2) := 
  λ i : fin (n1 + n2), if i.val < n1 then a1 ⟨ i.1, sorry ⟩ else a2 ⟨ i.1 - n1, sorry ⟩ 

def a5k := foo ℚ (a2k) (a3k)

#check (a5k)

def a10k := foo ℚ (a5k) (a5k)
#check a10k 





