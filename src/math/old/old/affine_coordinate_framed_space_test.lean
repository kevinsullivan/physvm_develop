import .affine_coordinate_framed_space
import .affine_space_type
import data.real.basic
import linear_algebra.affine_space.basic
import .affine_coordinate_space_lib

noncomputable theory
open aff_fr


/-
For now we'll work with real 3-spaces
-/
def dim := 3            -- pick whatever dimension you want here (other than 0? TODO: Check)
abbreviation K := ℝ     -- alternative field could be ℚ for example

/-
Type aliases for vector and point types in raw (frameless) K-dim affine coordinate space
-/
abbreviation aff_vec_coords := (aff_vec_coord_tuple K dim)
abbreviation aff_pt_coords := (aff_pt_coord_tuple K dim)

/-
Create a "raw" standard frame to bootstrap framed coordinate spaces, using

-/
def std_frame_on_raw_coord_space : affine_frame aff_pt_coords K aff_vec_coords (fin dim) := 
    aff_coord_space_std_frame K dim

#check std_frame_on_raw_coord_space

/-
Define type aliases for, respectively, the types of vectors and points with
coordinates in terms of the *raw* standard frame.
-/
abbreviation K_dim_raw_std_fr_vec := aff_coord_vec aff_pt_coords K aff_vec_coords dim (fin dim) std_frame_on_raw_coord_space
abbreviation K_dim_raw_std_fr_pt := aff_coord_pt aff_pt_coords K aff_vec_coords dim (fin dim) std_frame_on_raw_coord_space


/-
Create unframed standard basis vectors and origin points.
-/
def aff_pt_coords1 : aff_pt_coords :=       ⟨[1,0,0,0],sorry,sorry⟩
def aff_vec_coords1 : aff_vec_coords :=     ⟨[0,1,0,0],sorry,sorry⟩
def aff_vec_coords2 : aff_vec_coords :=     ⟨[0,0,1,0],sorry,sorry⟩
def aff_vec_coordsdim : aff_vec_coords :=   ⟨[0,0,0,1],sorry,sorry⟩


/-

structure aff_coord_pt (fr : affine_frame X K V ι) extends aff_pt_coord_tuple K n :=
   -- (tuple : aff_pt_coord_tuple K n)
   mk ::

structure aff_coord_vec (fr : affine_frame X K V ι) extends aff_vec_coord_tuple K n  :=
   -- (tuple : aff_vec_coord_tuple K n)
   mk ::
-/

/-
Lift unframed vectors and point to vectors and point with the raw standard frame
-/
def K_dim_raw_std_fr_vec1 : K_dim_raw_std_fr_vec := ⟨aff_vec_coordsdim⟩
def K_dim_raw_std_fr_vec2 : K_dim_raw_std_fr_vec := ⟨aff_vec_coords1⟩
def K_dim_raw_std_fr_vecdim : K_dim_raw_std_fr_vec := ⟨aff_vec_coords2⟩
def K_dim_raw_std_fr_pt1 : K_dim_raw_std_fr_pt := ⟨aff_pt_coords1⟩

/-
(fin n ) → "My Vector Type"
-/

/-
Define a function to assemble basis vectors into a *basis*
TODO: Fix this. Wrong level of abstraction at this point.
-/
def to_basis (n:ℕ) {vec_type : Type*} (l : vector vec_type n) 
    : (fin n) → vec_type := 
    λ i : fin n, l.nth i


/-
Create a standard frame whose points and vectors themselves have frames, namely
the raw standard frame.
-/ 
def std_frame_complete : affine_frame K_dim_raw_std_fr_pt K K_dim_raw_std_fr_vec (fin dim) := 
    ⟨K_dim_raw_std_fr_pt1, to_basis dim ⟨[K_dim_raw_std_fr_vec1,K_dim_raw_std_fr_vec2,K_dim_raw_std_fr_vecdim],sorry⟩,sorry⟩


/-
Abbreviations for points and vectors in the complete standard frame. The points
and vectors in this complete frame are themselves framed in the raw frame.
-/
abbreviation K_dim_std_frame_complete_vec := 
    aff_coord_vec K_dim_raw_std_fr_pt K K_dim_raw_std_fr_vec dim (fin dim) std_frame_complete
abbreviation K_dim_std_frame_complete_pt := 
    aff_coord_pt K_dim_raw_std_fr_pt K K_dim_raw_std_fr_vec dim (fin dim) std_frame_complete


/-
TODO: Do we want to create a standard frame for A_dim whose points and vectors
are themselves expressed in terms of this standard frame?
-/


/-
Create basis vectors and points in the complete standard frame suitable for
constructing a derived, non-standard frame. Note that the basis vectors in
this case are in different order than 1, 2, dim (now 2, dim, 1).
-/
def K_dim_std_frame_complete_vec1 : K_dim_std_frame_complete_vec := ⟨aff_vec_coords2⟩
def K_dim_std_frame_complete_vec2 : K_dim_std_frame_complete_vec := ⟨aff_vec_coordsdim⟩
def K_dim_std_frame_complete_vecdim : K_dim_std_frame_complete_vec := ⟨aff_vec_coords1⟩
def K_dim_std_frame_complete_pt1 : K_dim_std_frame_complete_pt := ⟨aff_pt_coords1⟩


/-
Use the point and vectors just created to create a non-standard frame.
-/
def non_standard_frame : affine_frame K_dim_std_frame_complete_pt K K_dim_std_frame_complete_vec (fin dim) := 
    ⟨K_dim_std_frame_complete_pt1,to_basis dim ⟨[K_dim_std_frame_complete_vec1,K_dim_std_frame_complete_vec2,K_dim_std_frame_complete_vecdim],sorry⟩,sorry⟩
    

/-
Abbreviations for points and vectors in this new non-standard frame
-/
abbreviation K_dim_non_standard_frame_vec := 
    aff_coord_vec K_dim_std_frame_complete_pt K K_dim_std_frame_complete_vec dim (fin dim) non_standard_frame
abbreviation K_dim_non_standard_frame_pt := 
    aff_coord_pt K_dim_std_frame_complete_pt K K_dim_std_frame_complete_vec dim (fin dim) non_standard_frame

/-
Some points and vectors in this non-standard frame. (Note that in all cases we're using
raw affine points and vectors to supply coordinate tuples for all of these constructors.)
-/
def K_dim_non_standard_frame_vec1 : K_dim_non_standard_frame_vec := ⟨aff_vec_coords2⟩
def K_dim_non_standard_frame_vec2 : K_dim_non_standard_frame_vec := ⟨aff_vec_coordsdim⟩
def K_dim_non_standard_frame_vecdim : K_dim_non_standard_frame_vec := ⟨aff_vec_coords1⟩
def K_dim_non_standard_frame_pt1 : K_dim_non_standard_frame_pt := ⟨aff_pt_coords1⟩

/-
Test out type checking of affine space algebraic operations: expect succeed.
-/
def vecsub := K_dim_non_standard_frame_vec1 - K_dim_non_standard_frame_vec2 -- expected :pass
def vecptadd := pt_plus_vec K_dim_non_standard_frame_pt1 K_dim_non_standard_frame_vec2 --expected : pass
def vecptaddnotation := K_dim_non_standard_frame_pt1 +ᵥ K_dim_non_standard_frame_vec2 --expected : pass
def ptvecadd := K_dim_non_standard_frame_vec2 +ᵥ K_dim_non_standard_frame_pt1 --expected : pass
def vecptsub := K_dim_non_standard_frame_pt1 -ᵥ K_dim_non_standard_frame_vec2  --K_dim_non_standard_frame_pt1 -ᵥ K_dim_non_standard_frame_vec2 --expected : pass
def pt_sub := K_dim_non_standard_frame_pt1 -ᵥ K_dim_non_standard_frame_pt1 -- expected : pass
def scaled : K_dim_non_standard_frame_vec  := (1:K)•K_dim_non_standard_frame_vec2 

/-
Test type checking of affine space operations: expect fail.
-/
def ptvecsub := K_dim_non_standard_frame_vec2 -ᵥ K_dim_non_standard_frame_pt1 -- expected : fail?
def pt_add := K_dim_non_standard_frame_pt1 +ᵥ K_dim_non_standard_frame_pt1 -- expected : fail
def dif_fr := K_dim_std_frame_complete_vec1 - K_dim_non_standard_frame_vec2 -- expected : fail

/-
SUMMARY:

We have two frames:

- K_dim_std_frame_complete_vec [points and vectors of the frame are framed in raw frame]
- K_dim_non_standard_frame_vec [points and vectors of the frame are framed in K_dim_std_frame_complete_vec]

Observation: We have frames but we don't have explicit corresponding affine spaces. (Or do we?)
-/

/-
Define affine spaces with increasingly structured frames. 
- The unframed space is a raw affine coordinate space with no explicit frame.
- The raw_std space imposes a frame on this space whose points and vectors in the unframed space.
- The quasi-framed space imposes a frame on this space whose points and vectors are in the raw_std space
- The fully framed space imposes a frame whose points and vectors are in the quasi-framed (compl) space. 
-/
def an_unframed_affine_space : affine_space_type aff_pt_coords K aff_vec_coords := ⟨⟩ 
def a_raw_std_framed_affine_space : affine_space_type K_dim_raw_std_fr_pt K K_dim_raw_std_fr_vec := ⟨⟩
def a_quasi_framed_affine_space : affine_space_type K_dim_std_frame_complete_pt K K_dim_std_frame_complete_vec := ⟨⟩
def a_fully_framed_affine_space : affine_space_type K_dim_non_standard_frame_pt K K_dim_non_standard_frame_vec := ⟨⟩


/-
Now we'll build two more spaces on top of fully_framed
- derived_frame and derived_space
- derived_frame_2 and derived_space_2
-/


/-
Here's derived_frame and derived space
-/
def derived_frame := 
    aff_lib.affine_coord_nspace.mk_derived_frame
    a_fully_framed_affine_space
            ⟨aff_pt_coords1⟩ 
            ⟨[⟨aff_vec_coordsdim⟩,⟨aff_vec_coords2⟩,⟨aff_vec_coords1⟩],
                    by refl⟩
                
def derived_space :=
    aff_lib.affine_coord_nspace.mk_derived_from_frame
        a_fully_framed_affine_space
        derived_frame


-- Here's derived_frame_2 with points made in derived_space, followed by derived_space_2
def my_pt := aff_lib.affine_coord_nspace.mk_point derived_space [1,1,1]
def my_v1 := aff_lib.affine_coord_nspace.mk_vec derived_space [0.5,0,0]
def my_v2 := aff_lib.affine_coord_nspace.mk_vec derived_space [0,0.5,1]
def my_v3 := aff_lib.affine_coord_nspace.mk_vec derived_space [0,0,0.5]


def derived_frame_2 := 
    aff_lib.affine_coord_nspace.mk_derived_frame
    derived_space
            (aff_lib.affine_coord_nspace.mk_point derived_space [1,1,1]) 
            ⟨
                [
                    (aff_lib.affine_coord_nspace.mk_vec derived_space [0.5,0,0]),
                    (aff_lib.affine_coord_nspace.mk_vec derived_space [0,0.5,1]),
                    (aff_lib.affine_coord_nspace.mk_vec derived_space [0,0,0.5])
                ], 
                by refl
            ⟩


def derived_space_2 :=
   aff_lib.affine_coord_nspace.mk_derived_from_frame
        derived_space
        derived_frame_2

/-
Given a space returns its base frame (or space), i.e., the frame in terms of which
its frame elements are expressed.
-/

/-

def an_unframed_affine_space 
    : affine_space_type aff_pt_coords K aff_vec_coords 
    := ⟨⟩ 
def a_raw_std_framed_affine_space : affine_space_type K_dim_raw_std_fr_pt K K_dim_raw_std_fr_vec := ⟨⟩
def a_quasi_framed_affine_space : affine_space_type K_dim_std_frame_complete_pt K K_dim_std_frame_complete_vec := ⟨⟩
def a_fully_framed_affine_space : affine_space_type K_dim_non_standard_frame_pt K K_dim_non_standard_frame_vec := ⟨⟩



- get_base_space derived_space_2
                    (affine_space aff_coord_pt K aff_coord_vec der_fr) 
                    :          
        -- expect derived_space
- get_base_space derived_space          
        -- expect a_fully_framed_affine_space
- get_base_space a_fully_framed_affine_space 
                    (affine_space aff_coord_pt K aff_coord_vec quasi_fr)           
        -- expect a_quasi_framed_affine_space
- get_base_space a_quasi_framed_affine_space 
                     (affine_space aff_coord_pt K aff_coord_vec raw_fr)           
        -- expect a_raw_std_framed_affine_space
- get_base_space a_raw_std_framed_affine_space 
                     (affine_space aff_coord_pt K aff_coord_vec unfr_fr)    
        -- expect an_unframed_affine_space
- get_base_space an_unframed_affine_space 
                    : (affine_space tuple_pt K tuple_vec )
        -- expect ???
-/

#check derived_space_2
#check (aff_lib.affine_coord_nspace dim derived_frame_2)

/-
aff coord space:
    
    affine_space_type 
        (aff_coord_pt X K V n ι fr)
        K
        (aff_coord_vec X K V n ι fr)

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

-/



def derived_space_2_base := aff_lib.affine_coord_space.get_base_space derived_space_2

example : derived_space_2_base = derived_space := rfl       -- nope

def derived_space_base := aff_lib.affine_coord_space.get_base_space derived_space

def a_fully_framed_affine_space_base := aff_lib.affine_coord_space.get_base_space a_fully_framed_affine_space

def another_base := aff_lib.affine_coord_space.get_base_space a_fully_framed_affine_space

def a_quasi_framed_affine_space_base := aff_lib.affine_coord_space.get_base_space a_fully_framed_affine_space

def a_raw_framed_affine_space_base := aff_lib.affine_coord_space.get_base_space a_fully_framed_affine_space


#check derived_space_2_base
/-
    affine_space_type 
        (aff_coord_pt X K V n (fin n) fr)
        K
        (aff_coord_vec X K V n (fin n) fr)
-/


/-
inductive affine_coordinate_space_type
| mk_raw (as : affine_space aff_pt K aff_vec) (o : origin) 
| mk_der (acs : affine_coordinate_space_type) (acf: affine_coordinate_frame)
-/


