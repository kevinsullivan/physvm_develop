import .affine_space_type
import .affine_frame
import data.real.basic

def reals_as_affine_space := affine_space_type
    ℝ 
    ℝ 
    ℝ

#check reals_as_affine_space

def reals_as_affine_space_1 : reals_as_affine_space  := ⟨⟩
def reals_as_affine_space_2 : reals_as_affine_space  := ⟨⟩

example : reals_as_affine_space_1 = reals_as_affine_space_2 := rfl

def a_frame : affine_frame ℝ ℝ ℝ (fin 1) :=
⟨(0 : ℝ),
(λ (n : fin 1), 1),
sorry ⟩ 





/-
A few things to note:

(1) We can specialize our generic affine_space_type definition
(2) We can't instantiate disjoint affine space of the same type 
(3) Can we express news points and vectors in terms of this frame?
-/