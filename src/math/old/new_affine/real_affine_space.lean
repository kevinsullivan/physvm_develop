import linear_algebra.affine_space.basic
import ..new_affine.affine_coordinate_space
import data.real.basic


namespace real_affine

abbreviation real_vec := aff_vec ℝ
abbreviation real_pt  := aff_pt  ℝ

abbreviation r3_vec := real_vec 3
abbreviation r3_pt  := real_pt  3

universes u v w

structure aff_struct :=
(X : Type u)
(K : Type v)
(V : Type w)
(fld : ring K)
(grp : add_comm_group V)
(vec : module K V)
(aff : affine_space V X)

structure vec_struct :=
(K : Type u)
(V : Type v)
(fld : field K)
(grp : add_comm_group V)
(vec : vector_space K V)

inductive Algebra  
| aff_space (a : aff_struct)
| vec_space (v : vec_struct)
| nat_monoid -- placeholder, commutative monoid with monus operator

def real_aff_pt_n := λn : ℕ, aff_pt ℝ n
def real_scalar := ℝ
def real_aff_vec_n := λn : ℕ, aff_vec ℝ n
def prf_ring := real.ring
def prf_real_add_comm_grp_n := λn : ℕ, aff_comm_group ℝ n
def prf_vec_module_n := λn : ℕ, aff_module ℝ n
def prf_aff_crd_sp := λn : ℕ, aff_coord_is ℝ n

    --⟨aff_pt ℝ n, ℝ, aff_vec ℝ n, real.ring, aff_comm_group ℝ n, aff_module ℝ n, aff_coord_is ℝ n⟩
def to_affine : ℕ → aff_struct := λ n,
    ⟨real_aff_pt_n n, ℝ , (real_aff_vec_n n), real.ring, prf_real_add_comm_grp_n n,prf_vec_module_n n,prf_aff_crd_sp n⟩


noncomputable def to_vector : ℕ → vec_struct := λ n, 
    ⟨ℝ, aff_vec ℝ n, real.field, aff_comm_group ℝ n, aff_module ℝ n⟩

end real_affine