import .affine_coordinate_framed_space_11_16
import .affine_space_type
import .list_as_k_tuple
universes u v w

namespace aff_lib

open aff_fr
variables 
    (K : Type v) 
    (n : ℕ) 
    [inhabited K] 
    [field K] 
    --(fr : affine_tuple_coordinate_frame K n)
    (fr : affine_coordinate_frame K n)
/-
structure affine_coord_space
    (K : Type v) 
    (n : ℕ) 
    [inhabited K] 
    [field K]  
| simple
    {fr : affine_tuple_coordinate_frame K n}
    (sp :
    affine_space_type 
        (aff_coord_pt K n fr)
        K
        (aff_coord_vec K n fr)) : affine_coord_space
| derived  
    {der : affine_derived_coordinate_frame K n}
    (sp :
    affine_space_type 
        (aff_coord_pt K n ↑der)
        K
        (aff_coord_vec K n ↑der)) : affine_coord_space
-/
def affine_coord_space :=
    affine_space_type 
        (aff_coord_pt K n fr)
        K
        (aff_coord_vec K n fr)

def affine_tuple_basis :=
    (fin n) → aff_vec_coord_tuple K n

def affine_coord_basis :=
    (fin n) → aff_coord_vec K n fr

/-
Helper method to retrieve the origin of coordinate space defined in
terms of a particular frame (which has an origin that we need to retrieve)
-/

abbreviation zero := vecl.zero_vector K n

def list.to_basis_vec : fin n → list K := λ x, (zero K n).update_nth (x.1 + 1) 1

lemma len_basis_vec_fixed (x : fin n) : (list.to_basis_vec K n x).length = n + 1 := sorry

lemma head_basis_vec_fixed (x : fin n) : (list.to_basis_vec K n x).head = 0 := sorry

def std_basis : fin n → aff_vec_coord_tuple K n :=
λ x, ⟨list.to_basis_vec K n x, len_basis_vec_fixed K n x, head_basis_vec_fixed K n x⟩

def affine_coordinate_frame.standard : affine_coordinate_frame K n := 
    (affine_coordinate_frame.tuple ⟨pt_zero K n, std_basis K n, sorry⟩)

def affine_coordinate_frame.base_frame : affine_coordinate_frame K n → affine_coordinate_frame K n
| (affine_coordinate_frame.tuple base) := affine_coordinate_frame.standard K n
| (affine_coordinate_frame.derived _ _ _ fr) := fr

def affine_coordinate_frame.origin_coords : affine_coordinate_frame K n → aff_pt_coord_tuple K n
| (affine_coordinate_frame.tuple base) := base.origin
| (affine_coordinate_frame.derived o _ _ _) := o


def affine_coordinate_frame.basis_coords 
    : affine_coordinate_frame K n → affine_tuple_basis K n
| (affine_coordinate_frame.tuple base) := base.basis
| (affine_coordinate_frame.derived _ b _ _) := b

/-
Helper method to retrieve the origin of ℕ-indexed coordinate space defined in
terms of a particular frame (which has an origin that we need to retrieve)
-/
def affine_coord_space.origin
    (sp : affine_coord_space K n fr)
    : aff_coord_pt K n (affine_coordinate_frame.base_frame K n fr)
    :=
        ⟨affine_coordinate_frame.origin_coords K n (affine_coordinate_frame.base_frame K n fr)⟩

/-
Helper method to retrieve the basis of coordinate space defined in
terms of a particular frame (which has a basis that we need to retrieve)
-/
def affine_coord_space.basis
    (sp : affine_coord_space K n fr)
    : affine_coord_basis K n (affine_coordinate_frame.base_frame K n fr)
    :=
        λ i : fin n, ⟨(affine_coordinate_frame.basis_coords K n (affine_coordinate_frame.base_frame K n fr)) i⟩


def affine_coord_space.frame
    (sp : affine_coord_space K n fr)
    := 
        fr

def affine_coord_space.get_base_space
    (sp : affine_coord_space K n fr)
    :=
        affine_coord_space K n (affine_coordinate_frame.base_frame K n fr)

def affine_coord_space.mk_with_standard
    : affine_coord_space K n (affine_coordinate_frame.standard K n)
    := ⟨⟩

def affine_coord_space.mk_derived
    (sp : affine_coord_space K n fr)
    (pt : aff_coord_pt K n fr)
    (basis : affine_coord_basis K n fr)
    : affine_coord_space K n 
        (affine_coordinate_frame.derived pt.1 (λ i:fin n,(basis i).1) sorry fr)
    := ⟨⟩



--IGNORE ALL BELOW THIS











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