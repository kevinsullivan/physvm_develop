import .affnK
import linear_algebra.std_basis

/-
Framed points, vectors, frames
-/

open_locale affine

universes u 

section explicitK

variables 
(K : Type u) [field K] [inhabited K]
(dim : ℕ) 

/-
Frame built from primitive (fin n)-indexed maps pts and vecs.
Constructors are Base (standard) frame or a derived frame.
-/
inductive fm : Π (dim : ℕ) (id_vec : fin dim → ℕ), Type (u)
| base : Π (dim : ℕ) (id_vec : fin dim → ℕ), fm dim id_vec
| deriv 
    {dim : ℕ}
    {id_vec : fin dim → ℕ}
    (origin : pt_n K dim) 
    (basis : vec_n_basis K dim)
    (parent : fm dim id_vec)
    : fm dim id_vec

instance fm_i {id_vec : fin dim → ℕ} : inhabited (fm K dim id_vec) := ⟨fm.base _ _⟩

/-
Helper method to retrieve a "parent frame" from a frame.
For a base/standard frame, there is no "parent", so it is 
it's own parent. For a deriv, simply return the frame it 
was derived from
-/
@[simp]
def fm.parent 
{K : Type u} [field K] [inhabited K]
{dim : ℕ} {id_vec : fin dim → ℕ}
: fm K dim id_vec → fm K dim id_vec
| (fm.base dim id_vec) := (fm.base dim id_vec)
| (fm.deriv origin basis parent) := parent

/-
Origin of a frame. For a standard frame, it is the 0 pt, 
for a derived frame, the new origin was provided at instantiation.
-/
@[simp]
def fm.origin
{K : Type u} [field K] [inhabited K]
{dim : ℕ} {id_vec : fin dim → ℕ}  :
fm K dim id_vec → pt_n K dim
| (fm.base dim id_vec) := (λi, mk_pt K 0)
| (fm.deriv origin basis parent) := origin

/-
Basis of a frame. For a standard frame, it is the standard basis, 
for a derived frame, the basis was provided at instantiation.
-/
@[simp]
def fm.basis 
{K : Type u} [field K] [inhabited K]
{dim : ℕ} {id_vec : fin dim → ℕ} :
fm K dim id_vec → (vec_n_basis K dim)
| (fm.base dim id_vec) := ⟨(λ i j, if j = i then mk_vec K 1 else mk_vec K 0), sorry, sorry⟩
| (fm.deriv origin basis parent) := (basis)


/-
Make a derived frame from an existing frame.
Arguments are (unframed) origin, (unframed) basis,
and parent frame.
-/
def mk_fm  {dim : ℕ} {id_vec : fin dim → ℕ}  (p : pt_n K dim) (b : vec_n_basis K dim) (f : fm K dim id_vec)
    : fm K dim id_vec:= fm.deriv p b f

/-
Helper function used to merge two frames when creating a product 
space from two lower dimensional spaces. The result of this function 
will be a block matrix which contains the two lower dimensional 
frames along the diagonal.
-/
@[simp]
def merge_prod_fm 
    {K : Type u} [inhabited K] [field K] 
    {dim1 : ℕ} {id_vec1 : fin dim1 → ℕ} --(f1 : fm K dim1 id_vec1)
    {dim2 : ℕ} {id_vec2 : fin dim2 → ℕ} --(f2 : fm K dim2 id_vec2)
    :  fm K dim1 id_vec1 → fm K dim2 id_vec2 → fm K (dim1+dim2) (add_maps id_vec1 id_vec2)
| (fm.deriv o1 b1 p1) (fm.deriv o2 b2 p2) := fm.deriv (add_maps o1 o2) 
        ⟨(λi, 
            if lt:i.1<dim1 then (add_maps (b1.basis_vecs ⟨i.1, lt⟩) (mk_vec_n K dim2 ⟨list.repeat 0 dim2, by simp only [list.length_repeat]⟩))
            else if lt:i.1-dim1<dim2 then (add_maps (mk_vec_n K dim1 ⟨list.repeat 0 dim1, by simp only [list.length_repeat]⟩) (b2.basis_vecs ⟨i.1 - dim1,lt⟩))
            else 0)
         ,sorry, sorry⟩ (merge_prod_fm p1 p2)
| (fm.deriv o1 b1 p1) (fm.base dim2 id_vec2) := fm.deriv (add_maps o1 (fm.base dim2 id_vec2).origin) 
        ⟨(λi, 
            if lt:i.1 < dim1 then (add_maps (b1.basis_vecs ⟨i.1, lt⟩) (mk_vec_n K dim2 ⟨list.repeat 0 dim2, by simp only [list.length_repeat]⟩))
            else if lt:i.1-dim1<dim2 then (add_maps (mk_vec_n K dim1 ⟨list.repeat 0 dim1, by simp only [list.length_repeat]⟩) ((fm.base dim2 id_vec2).basis.basis_vecs ⟨i.1 - dim1,lt⟩))
            else 0)
         ,sorry, sorry⟩ (merge_prod_fm p1 (fm.base dim2 id_vec2))
| (fm.base dim1 id_vec1) (fm.deriv o2 b2 p2) := fm.deriv (add_maps (fm.base dim1 id_vec1).origin o2) 
        ⟨(λi, 
            if lt:i.1<dim1 then (add_maps ((fm.base dim1 id_vec1).basis.basis_vecs ⟨i.1,lt⟩) (mk_vec_n K dim2 ⟨list.repeat 0 dim2, by simp only [list.length_repeat]⟩))
            else if lt:i.1-dim1<dim2 then (add_maps (mk_vec_n K dim1 ⟨list.repeat 0 dim1, by simp only [list.length_repeat]⟩) (b2.basis_vecs ⟨i.1-dim1,lt⟩))
            else 0)
         ,sorry, sorry⟩ (merge_prod_fm (fm.base dim1 id_vec1) p2)      
| (fm.base dim1 id_vec1) (fm.base dim2 id_vec2) := fm.base (dim1+dim2) (add_maps id_vec1 id_vec2)

/-
Our instantiation of an affine space. Note, it is essentially a 
wrapper around a frame, and thus does not have any underlying set. 
It is later used to parameterize framed points and vectors. Most
spaces will use the single constructor. The prod constructor can 
be used when trying to create the product of two lower dimensional
spaces.
-/
inductive spc : Π {dim : ℕ} {id_vec : fin dim → ℕ} (f: fm K dim id_vec), Type u
| single {dim : ℕ} {id_vec : fin dim → ℕ} (f: fm K dim id_vec) : spc f
| prod 
    {dim1 : ℕ} {id_vec1 : fin dim1 → ℕ} (f1: fm K dim1 id_vec1) --(s1 : spc dim1 id_vec1 f1)
    {dim2 : ℕ} {id_vec2 : fin dim2 → ℕ} (f2: fm K dim2 id_vec2) --(s2 : spc dim2 id_vec2 f2)
    : spc (merge_prod_fm f1 f2)                                 --(mk_prod_fm f1 f2)

/-
Helper function to retrieve frame from space (space is simply a wrapper around frame, anyway)
-/
def spc.fm {K : Type u} [inhabited K] [field K] {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} (sp : spc K f)
    := f
def spc.frame {K : Type u} [inhabited K] [field K] {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} (sp : spc K f)
    := f
@[reducible]
def spc.frame_type {K : Type u} [inhabited K] [field K] {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} (sp : spc K f)
    := fm K dim id_vec

/-
Alias for the default constructor of spc
-/
@[simp]
def mk_space  {K : Type u} [inhabited K] [field K] 
{dim : ℕ} {id_vec : fin dim → ℕ} 
    (f : fm K dim id_vec) : spc K f  :=
  spc.single f
  
/-
Alias for the prod constructor of spc
-/
@[simp]
def mk_prod_spc
    {K : Type u} [inhabited K] [field K] 
    {dim1 : ℕ} {id_vec1 : fin dim1 → ℕ} {f1 : fm K dim1 id_vec1} (s1 : spc K f1)
    {dim2 : ℕ} {id_vec2 : fin dim2 → ℕ} {f2 : fm K dim2 id_vec2} (s2 : spc K f2)
    : spc K (merge_prod_fm f1 f2) := spc.prod f1 f2



end explicitK

section implicitK

variables 
{K : Type u} [field K] [inhabited K] 
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} (s : spc K f)
{dim2 : nat } {id_vec2 : fin dim2 → nat} {f2 : fm K dim2 id_vec2} (s2 : spc K f2)

/-
A framed (parameterized by the space encapsulating the frame) point.
Contains an unframed point describing its coordinates. 
-/
@[ext]
structure point {f : fm K dim id_vec} (s : spc K f) :=
(coords : pt_n K dim)

/-
Constructor functions to make points
-/
@[simp]
def mk_point' (p : pt_n K dim) : point s := point.mk p  

@[simp]
def mk_point (coords_ : vector K dim) : point s := point.mk (mk_pt_n K dim coords_)  

/-
Combine two points to get their coordinate-wise cartesian product in a space that is
the product of the underlying respective spaces.
-/
@[simp]
def mk_point_prod  
    {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} {s : spc K f}  
    {dim2 : ℕ} {id_vec2 : fin dim2 → ℕ} {f2: fm K dim2 id_vec2} {s2 : spc K f2} 
    
    (p1 : point s) (p2 : point s2) : point (mk_prod_spc s s2)
    := ⟨add_maps p1.coords p2.coords⟩

@[simp]
def point.space {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} {s : spc K f} 
    (p : point s) : spc K _ := s
/-
A framed (parameterized by the space encapsulating the frame) vector.
Contains an unframed vector describing its coordinates. 
-/
@[ext]
structure vectr {f : fm K dim id_vec} (s : spc K f) :=
(coords : vec_n K dim)

/-
Same as for points, constructor functions and a product constructor.
-/
@[simp]
def mk_vectr' (p : vec_n K dim) : vectr s := vectr.mk p  
@[simp]
def mk_vectr (coords_ : vector K dim) : vectr s := vectr.mk (mk_vec_n K dim coords_)  

@[simp]
def mk_vectr_prod 
    {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} {s : spc K f}  
    {dim2 : ℕ} {id_vec2 : fin dim2 → ℕ} {f2: fm K dim2 id_vec2} {s2 : spc K f2} 
    (p1 : vectr s) (p2 : vectr s2) : vectr (mk_prod_spc s s2)
    := ⟨add_maps p1.coords p2.coords⟩

@[simp]
def vectr.space {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} {s : spc K f} 
    (v : vectr s) : spc K _ := s


end implicitK

