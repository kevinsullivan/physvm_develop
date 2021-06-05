
import data.real.basic
import ..affine.real_affine_coordinate_space_lib
import ..affine.affine_coordinate_framed_space

open aff_fr

universes u v w

namespace algebra

variables 
    (X : Type u) 
    (K : Type v) 
    (V : Type w) 
    (n : ℕ) 
    (k : K)
    (ι : Type*)
    (s : finset ι) 
    (g : ι → K) 
    (v : ι → V) 
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    [is_basis K v] 
    [affine_space V X]

inductive Algebra  
    {X : Type u} {V : Type w}
    [add_comm_group V] 
    [module ℝ V] 
    [vector_space ℝ V] 
    [affine_space V X]
    {n : ℕ}
| aff_sp 
    {fr : affine_frame X ℝ V (fin n) } 
    (v : aff_coord_vec X ℝ V n (fin n) fr)
    (a : real_lib.real_affine_coord_nspace n fr) 
    : Algebra
| aff_fr (fr : affine_frame X ℝ V (fin n)) : Algebra

inductive AlgebraicVector
    {X : Type u}
    {K : Type v}
    {V : Type w}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X K V (fin n) }
| aff_vec 
    (v : aff_coord_vec X K V n (fin n) fr) : AlgebraicVector

inductive AlgebraicPoint
    {X : Type u}
    {K : Type v}
    {V : Type w}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X K V (fin n) }
| aff_vec 
    (v : aff_coord_pt X K V n (fin n) fr) : AlgebraicPoint

end algebra

--| nat_monoid -- placeholder, commutative monoid with monus operator
