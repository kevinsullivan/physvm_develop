import .affine_coordinate_framed_space
import .affine_space_type
universes u v w

namespace aff_lib

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

open aff_fr


--
/-
Type for a "naked tuple" space. I.e., we define a natural-number indexed
space without a frame on it. We use this space to construct 
a coordinatized space, where all frames are expressed explicitly
in terms of a specific frame, often/such as the standard frame.
-/
def affine_tuple_space
    (K : Type v)
    (n : ℕ)  
    [inhabited K] 
    [field K] 
    [add_comm_group (aff_vec_coord_tuple K n)] 
    [module K (aff_vec_coord_tuple K n)] 
    [vector_space K (aff_vec_coord_tuple K n)] 
    [affine_space (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n)]
    := 
    affine_space_type 
        (aff_pt_coord_tuple K n)
        K
        (aff_vec_coord_tuple K n)

/-
We define a type for a coordinate space. Frames of this coordinate space
are defined using an arbitrary indexing set.
-/
def affine_coord_space
    {X : Type u} {K : Type v} {V : Type w} {ι : Type*}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    (n : ℕ)
    (fr : affine_frame X K V ι )  
    := 
    affine_space_type 
        (aff_coord_pt X K V n ι fr)
        K
        (aff_coord_vec X K V n ι fr)

/-
A coordinate space whose indexing set is, again, a set of natural numbers
-/
def affine_coord_nspace
    {X : Type u} {K : Type v} {V : Type w}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    (n : ℕ)
    (fr : affine_frame X K V (fin n) )  
    := 
    affine_space_type 
        (aff_coord_pt X K V n (fin n) fr)
        K
        (aff_coord_vec X K V n (fin n) fr)

/-
Helper method to retrieve the origin of coordinate space defined in
terms of a particular frame (which has an origin that we need to retrieve)
-/
def affine_coord_space.origin 
    {X : Type u} {K : Type v} {V : Type w} {ι : Type*}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X K V ι }
    (sp : affine_coord_space n fr)
    :=
        fr.origin 

/-
Helper method to retrieve the origin of ℕ-indexed coordinate space defined in
terms of a particular frame (which has an origin that we need to retrieve)
-/
def affine_coord_nspace.origin 
    {X : Type u} {K : Type v} {V : Type w}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {n : ℕ}
     {fr : affine_frame X K V (fin n) }
    (sp : affine_coord_nspace n fr) 
    :=
        fr.origin 
/-
Helper method to retrieve the basis of coordinate space defined in
terms of a particular frame (which has a basis that we need to retrieve)
-/
def affine_coord_space.basis
    {X : Type u} {K : Type v} {V : Type w} { ι : Type*}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X K V ι }
    (sp : affine_coord_space n fr) 
    := 
        fr.basis 

def affine_coord_space.frame
    {X : Type u} {K : Type v} {V : Type w} {ι : Type*}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X K V ι }
    (sp : affine_coord_space n fr) 
    := 
        fr

def affine_coord_space.get_base_space
    {X : Type u} {K : Type v} {V : Type w} {ι : Type*}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X K V ι }
    (sp : affine_coord_space n fr)
    :=
        affine_space_type X K V

/-
Helper method to retrieve the basis of ℕ-indexed coordinate space defined in
terms of a particular frame (which has a basis that we need to retrieve)
-/
def affine_coord_nspace.basis
    {X : Type u} {K : Type v} {V : Type w}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X K V (fin n) }
    (sp : affine_coord_nspace n fr) 
    := 
        fr.basis 



def affine_coord_nspace.frame
    {X : Type u} {K : Type v} {V : Type w}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X K V (fin n) }
    (sp : affine_coord_nspace n fr) 
    := 
        fr


/-
Given field and dimension, construct a raw affine tuple space
-/
def affine_tuple_space.mk_raw
    (K : Type v)
    (n : ℕ)  
    [inhabited K] 
    [field K] 
    [add_comm_group (aff_vec_coord_tuple K n)] 
    [module K (aff_vec_coord_tuple K n)] 
    [vector_space K (aff_vec_coord_tuple K n)] 
    [affine_space (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n)]
    :affine_tuple_space K n 
    := 
    ⟨⟩

/-
Construct an affine coordinate space from a raw tuple space by selecting
an appropriate origin and a basis. The frame of the coordinate space is
defined in terms of the tuple space
-/
def affine_coord_nspace.mk_from_raw 
   {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    [add_comm_group (aff_vec_coord_tuple K n)] 
    [module K (aff_vec_coord_tuple K n)] 
    [vector_space K (aff_vec_coord_tuple K n)] 
    [affine_space (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n)]
    (sp : affine_tuple_space K n ) 
    (origin : aff_pt_coord_tuple K n) 
    (basis : fin n → (aff_vec_coord_tuple K n)) :
    affine_coord_nspace n (⟨origin,basis,sorry⟩:affine_frame (aff_pt_coord_tuple K n) (K) (aff_vec_coord_tuple K n) (fin n))  :=
    ⟨⟩
/-
Construct a derived space of a ℕ-index coordinate space by selling an
origin and a basis in the original coordinate space. 
-/

def affine_coord_nspace.mk_derived_from_basis
    {X : Type u} {K : Type v} {V : Type w}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {n : ℕ}
    {f : affine_frame X K V (fin n) }
    (sp : affine_coord_space n f) 
    (origin : aff_coord_pt X K V n (fin n) f) 
    (basis : fin n → (aff_coord_vec X K V n (fin n) f)) 
    : affine_coord_nspace n (⟨origin, basis, sorry⟩ : affine_frame 
                (aff_coord_pt X K V n (fin n) f) 
                (K) 
                (aff_coord_vec X K V n (fin n) f) (fin n)) :=
    ⟨⟩

def affine_coord_nspace.mk_derived
    {X : Type u} {K : Type v} {V : Type w}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {n : ℕ}
    {f : affine_frame X K V (fin n) }
    (sp : affine_coord_space n f) 
    (origin : aff_coord_pt X K V n (fin n) f) 
    (basis : vector (aff_coord_vec X K V n (fin n) f) n) 
    : affine_coord_nspace n (⟨origin, (λ i : fin n, basis.nth i), sorry⟩ : affine_frame 
                (aff_coord_pt X K V n (fin n) f) 
                (K) 
                (aff_coord_vec X K V n (fin n) f) (fin n)) :=
    ⟨⟩


def affine_coord_nspace.mk_derived_from_frame
    {X : Type u} {K : Type v} {V : Type w}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {n : ℕ}
    {f : affine_frame X K V (fin n) }
    (sp : affine_coord_space n f) 
    (f : affine_frame 
                (aff_coord_pt X K V n (fin n) f) 
                (K) 
                (aff_coord_vec X K V n (fin n) f) (fin n))
    : affine_coord_nspace n f :=
    ⟨⟩

    

def affine_coord_nspace.mk_derived_frame
    {X : Type u} {K : Type v} {V : Type w}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X K V (fin n) }
    (sp : affine_coord_space n fr) 
    (origin : aff_coord_pt X K V n (fin n) fr) 
    (basis : vector (aff_coord_vec X K V n (fin n) fr) n)  :
    affine_frame 
        (aff_coord_pt X K V n (fin n) fr) 
        K 
        (aff_coord_vec X K V n (fin n) fr) 
        (fin n):=
    ⟨origin, (λ i : fin n, basis.nth i), sorry⟩ 

def affine_coord_nspace.mk_derived_frame_with_basis
    {X : Type u} {K : Type v} {V : Type w}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X K V (fin n) }
    (sp : affine_coord_space n fr) 
    (origin : aff_coord_pt X K V n (fin n) fr) 
    (basis : fin n → (aff_coord_vec X K V n (fin n) fr)) :
    affine_frame 
        (aff_coord_pt X K V n (fin n) fr) 
        K 
        (aff_coord_vec X K V n (fin n) fr) 
        (fin n):=
    ⟨origin, basis, sorry⟩

 

/-
Helper to make a point in a ℕ-index coordinate space by supplying just a
space and coordinates.
-/
def affine_coord_nspace.mk_point
    {X : Type u} {K : Type v} {V : Type w}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {n : ℕ}
    {fr : affine_frame X K V (fin n) }
    (sp : affine_coord_space n fr) 
    (coords : list K)  :
    (aff_coord_pt X K V n (fin n) fr) :=
    ⟨⟨[1]++coords, sorry, sorry⟩⟩

/-
Helper to make a vector in a ℕ-index coordinate space by supplying just a
space and coordinates.
-/
def affine_coord_nspace.mk_vec
    {X : Type u} {K : Type v} {V : Type w}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {n : ℕ}
     {fr : affine_frame X K V (fin n) }
    (sp : affine_coord_space n fr) 
    (coords : list K)  :
    (aff_coord_vec X K V n (fin n) fr) :=
    ⟨⟨[0]++coords, sorry, sorry⟩⟩

#check list.nth

/-
Constructs a coordinate n-space where it's frame is the standard frame, 
and the standard frame is expressed in terms of the standard frame.
It does so by constructing a raw space, using that to construct a coordinate space with the standard frame,
and then nesting the coordinate space inside another coordinate space.
-/
def affine_coord_nspace.mk_with_standard_frame
    (K : Type v)
    (n : ℕ)  
    [inhabited K] 
    [field K] 
    [add_comm_group (aff_vec_coord_tuple K n)] 
    [module K (aff_vec_coord_tuple K n)] 
    [vector_space K (aff_vec_coord_tuple K n)] 
    [affine_space (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n)]
    :=
    let sp_raw := (affine_tuple_space.mk_raw K n) in
            let sp_raw_wrapper_as_coord_nspace := 
            (affine_coord_nspace.mk_from_raw
                sp_raw
                ⟨[1,0,0,0],sorry,sorry⟩
                (λ i:(fin n), ⟨[0,0,0,0].update_nth i.1 1,sorry,sorry⟩))
                    in
                affine_coord_nspace.mk_derived_from_basis
                    sp_raw_wrapper_as_coord_nspace
                        ⟨affine_coord_nspace.origin sp_raw_wrapper_as_coord_nspace⟩
                        (λ i:(fin n), ⟨⟨[0,0,0,0].update_nth i.1 1,sorry,sorry⟩⟩)

end aff_lib