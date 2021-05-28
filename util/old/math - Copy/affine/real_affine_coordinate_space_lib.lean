import .affine_coordinate_space_lib
import data.real.basic
import .affine_space_type


namespace real_lib

universes u w

noncomputable theory

open aff_fr
open aff_lib

/-
ℝ
Type for a "naked tuple" space. I.e., we define a natural-number indexed
space without a frame on it. We use this space to construct 
a coordinatized space, where all frames are expressed explicitly
in terms of a specific frame, often/such as the standard frame.
-/
def real_affine_tuple_space
    (n : ℕ)  
    [add_comm_group (aff_vec_coord_tuple ℝ n)] 
    [module ℝ (aff_vec_coord_tuple ℝ n)] 
    [vector_space ℝ (aff_vec_coord_tuple ℝ n)] 
    [affine_space (aff_vec_coord_tuple ℝ n) (aff_pt_coord_tuple ℝ n)]
    := 
    affine_space_type 
        (aff_pt_coord_tuple ℝ n)
        ℝ
        (aff_vec_coord_tuple ℝ n)

/-
We define a type for a coordinate space. Frames of this coordinate space
are defined using an arbitrary indexing set.
-/
def real_affine_coord_space
    {X : Type u} {V : Type w} {ι : Type*}
    [add_comm_group V] 
    [module ℝ V] 
    [vector_space ℝ V] 
    [affine_space V X]
    (n : ℕ)
    (fr : affine_frame X ℝ V ι )  
    := 
    affine_coord_space n fr
   -- affine_space_type 
    --    (aff_coord_pt X ℝ V n ι fr)
    --    ℝ
     --   (aff_coord_vec X ℝ V n ι fr)

/-
A coordinate space whose indexing set is, again, a set of natural numbers
-/
def real_affine_coord_nspace
    {X : Type u} {V : Type w}
    [add_comm_group V] 
    [module ℝ V] 
    [vector_space ℝ V] 
    [affine_space V X]
    (n : ℕ)
    (fr : affine_frame X ℝ V (fin n) )  
    := 
    affine_coord_nspace n fr

def real_affine_coord_nframe
    {X : Type u} {V : Type w}
    [add_comm_group V] 
    [module ℝ V] 
    [vector_space ℝ V] 
    [affine_space V X]
    {n : ℕ}
    :=
     affine_frame X ℝ V (fin n)

/-
Helper method to retrieve the origin of coordinate space defined in
terms of a particular frame (which has an origin that we need to retrieve)
-/
def real_affine_coord_space.origin 
    {X : Type u} {V : Type w} {ι : Type*}
    [add_comm_group V] 
    [module ℝ V] 
    [vector_space ℝ V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X ℝ V ι }
    (sp : affine_coord_space n fr)
    :=
        fr.origin 

/-
Helper method to retrieve the origin of ℕ-indexed coordinate space defined in
terms of a particular frame (which has an origin that we need to retrieve)
-/
def real_affine_coord_nspace.origin 
    {X : Type u} {V : Type w}
    [add_comm_group V] 
    [module ℝ V] 
    [vector_space ℝ V] 
    [affine_space V X]
    {n : ℕ}
     {fr : affine_frame X ℝ V (fin n) }
    (sp : affine_coord_nspace n fr) 
    :=
        fr.origin 
/-
Helper method to retrieve the basis of coordinate space defined in
terms of a particular frame (which has a basis that we need to retrieve)
-/
def real_affine_coord_space.basis
    {X : Type u} {V : Type w} { ι : Type*}
    [add_comm_group V] 
    [module ℝ V] 
    [vector_space ℝ V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X ℝ V ι }
    (sp : affine_coord_space n fr) 
    := 
        fr.basis 

/-
Helper method to retrieve the basis of ℕ-indexed coordinate space defined in
terms of a particular frame (which has a basis that we need to retrieve)
-/
def real_affine_coord_nspace.basis
    {X : Type u} {V : Type w}
    [add_comm_group V] 
    [module ℝ V] 
    [vector_space ℝ V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X ℝ V (fin n) }
    (sp : affine_coord_nspace n fr) 
    := 
        fr.basis 

def real_affine_coord_nspace.frame
    {X : Type u} {V : Type w}
    [add_comm_group V] 
    [module ℝ V] 
    [vector_space ℝ V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X ℝ V (fin n) }
    (sp : affine_coord_nspace n fr) 
    := 
        fr
/-
Given field and dimension, construct a raw affine tuple space
-/
def real_affine_tuple_space.mk_raw
    (n : ℕ)  
    [add_comm_group (aff_vec_coord_tuple ℝ n)] 
    [module ℝ (aff_vec_coord_tuple ℝ n)] 
    [vector_space ℝ (aff_vec_coord_tuple ℝ n)] 
    [affine_space (aff_vec_coord_tuple ℝ n) (aff_pt_coord_tuple ℝ n)]
    :affine_tuple_space ℝ n 
    := 
    ⟨⟩

/-
Construct an affine coordinate space from a raw tuple space by selecting
an appropriate origin and a basis. The frame of the coordinate space is
defined in terms of the tuple space
-/
def real_affine_coord_nspace.mk_from_raw 
    {n : ℕ}
    [add_comm_group (aff_vec_coord_tuple ℝ n)] 
    [module ℝ (aff_vec_coord_tuple ℝ n)] 
    [vector_space ℝ (aff_vec_coord_tuple ℝ n)] 
    [affine_space (aff_vec_coord_tuple ℝ n) (aff_pt_coord_tuple ℝ n)]
    (sp : affine_tuple_space ℝ n ) 
    (origin : aff_pt_coord_tuple ℝ n) 
    (basis : fin n → (aff_vec_coord_tuple ℝ n)) :
    affine_coord_nspace n (⟨origin,basis,sorry⟩:affine_frame (aff_pt_coord_tuple ℝ n) (ℝ) (aff_vec_coord_tuple ℝ n) (fin n))  :=
    ⟨⟩
/-
Construct a derived space of a ℕ-index coordinate space by selling an
origin and a basis in the original coordinate space. 
-/
def real_affine_coord_nspace.mk_derived
    {X : Type u} {V : Type w}
    [add_comm_group V] 
    [module ℝ V] 
    [vector_space ℝ V] 
    [affine_space V X]
    {n : ℕ}
    {f : affine_frame X ℝ V (fin n) }
    (sp : affine_coord_space n f) 
    (origin : aff_coord_pt X ℝ V n (fin n) f) 
    (basis : fin n → (aff_coord_vec X ℝ V n (fin n) f)) 
    : affine_coord_nspace n (⟨origin, basis, sorry⟩ : affine_frame 
                (aff_coord_pt X ℝ V n (fin n) f) 
                (ℝ) 
                (aff_coord_vec X ℝ V n (fin n) f) (fin n)) :=
    ⟨⟩

    

def real_affine_coord_nspace.mk_derived_frame
    {X : Type u} {V : Type w}
    [add_comm_group V] 
    [module ℝ V] 
    [vector_space ℝ V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X ℝ V (fin n) }
    (sp : affine_coord_space n fr) 
    (origin : aff_coord_pt X ℝ V n (fin n) fr) 
    (basis : fin n → (aff_coord_vec X ℝ V n (fin n) fr)) :
    affine_frame 
        (aff_coord_pt X ℝ V n (fin n) fr) 
        ℝ 
        (aff_coord_vec X ℝ V n (fin n) fr) 
        (fin n):=
    ⟨origin, basis, sorry⟩

/-
Helper to make a point in a ℕ-index coordinate space by supplying just a
space and coordinates.
-/
def real_affine_coord_nspace.point
    {X : Type u} {V : Type w}
    [add_comm_group V] 
    [module ℝ V] 
    [vector_space ℝ V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X ℝ V (fin n) }
    (sp : affine_coord_space n fr)
     :=
    (aff_coord_pt X ℝ V n (fin n) fr)


def real_affine_coord_nspace.mk_point
    {X : Type u} {V : Type w}
    [add_comm_group V] 
    [module ℝ V] 
    [vector_space ℝ V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X ℝ V (fin n) }
    (sp : affine_coord_space n fr) 
    (coords : vector ℝ n)  :
    (aff_coord_pt X ℝ V n (fin n) fr) :=
    ⟨⟨[1]++coords.1, sorry, sorry⟩⟩

/-
Helper to make a vector in a ℕ-index coordinate space by supplying just a
space and coordinates.
-/
def real_affine_coord_nspace.vec
    {X : Type u} {V : Type w}
    [add_comm_group V] 
    [module ℝ V] 
    [vector_space ℝ V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X ℝ V (fin n) }
    (sp : affine_coord_space n fr)
     :=
    (aff_coord_vec X ℝ V n (fin n) fr)


def real_affine_coord_nspace.mk_vec
    {X : Type u} {V : Type w}
    [add_comm_group V] 
    [module ℝ V] 
    [vector_space ℝ V] 
    [affine_space V X]
    {n : ℕ}
     {fr : affine_frame X ℝ V (fin n) }
    (sp : affine_coord_space n fr) 
    (coords : vector ℝ n)  :
    (aff_coord_vec X ℝ V n (fin n) fr) :=
    ⟨⟨[0]++coords.1, sorry, sorry⟩⟩

#check list.nth

/-
Constructs a coordinate n-space where it's frame is the standard frame, 
and the standard frame is expressed in terms of the standard frame.
It does so by constructing a raw space, using that to construct a coordinate space with the standard frame,
and then nesting the coordinate space inside another coordinate space.
-/
def real_affine_coord_nspace.mk_with_standard_frame
    (n : ℕ)  
    [add_comm_group (aff_vec_coord_tuple ℝ n)] 
    [module ℝ (aff_vec_coord_tuple ℝ n)] 
    [vector_space ℝ (aff_vec_coord_tuple ℝ n)] 
    [affine_space (aff_vec_coord_tuple ℝ n) (aff_pt_coord_tuple ℝ n)]
    :=
    let sp_raw := (affine_tuple_space.mk_raw ℝ n) in
            let sp_raw_wrapper_as_coord_nspace := 
            (affine_coord_nspace.mk_from_raw
                sp_raw
                ⟨[1,0,0,0],sorry,sorry⟩
                (λ i:(fin n), ⟨[0,0,0,0].update_nth i.1 1,sorry,sorry⟩))
                    in
                affine_coord_nspace.mk_derived 
                    sp_raw_wrapper_as_coord_nspace
                        ⟨affine_coord_nspace.origin sp_raw_wrapper_as_coord_nspace⟩
                        (λ i:(fin n), ⟨⟨[0,0,0,0].update_nth i.1 1,sorry,sorry⟩⟩)

def real_affine_coord_nspace.get_standard (n :ℕ) :=
    real_affine_coord_nspace.frame (real_affine_coord_nspace.mk_with_standard_frame n)


end real_lib