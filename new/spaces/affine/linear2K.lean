import linear_algebra.affine_space.basic
import algebra.module.basic

universes u 

variables 
(K : Type u) [ring K] [inhabited K] [field K] --added field for vector space

def linear2 := prod K K

def lin2_add : linear2 K → linear2 K → linear2 K
| (f1,s1) (f2,s2) := ⟨ f1 + f2, s1 + s2 ⟩ 

def lin2_scale : K → linear2 K → linear2 K
| a (f,s) := ⟨ a * f, a * s ⟩ 

def lin2_neg : linear2 K → linear2 K
| (f,s) := ⟨ -1 * f, -1 * s ⟩ 

def lin2_sub :  linear2 K → linear2 K → linear2 K
| l1 l2 := lin2_add K l1 (lin2_neg K l2) 

instance : has_add (linear2 K) := ⟨ lin2_add K ⟩ 
instance : has_zero (linear2 K) := ⟨ (0,0) ⟩ 
instance : has_scalar K (linear2 K) := ⟨ lin2_scale K ⟩ 
instance : has_neg (linear2 K) := ⟨ lin2_neg K ⟩ 
instance : has_sub (linear2 K) := ⟨ lin2_sub K ⟩
instance : add_comm_group (linear2 K) := sorry
instance : module K (linear2 K) := sorry
--instance : field K := sorry
instance : vector_space K (linear2 K) := sorry
-- instance : 2D vector_space ...


