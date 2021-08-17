import .affine_coordinate_framed_space_lib --linear_algebra.affine_space.basic
import 
    linear_algebra.affine_space.affine_equiv 
    linear_algebra.nonsingular_inverse
    linear_algebra.matrix
--    linear_algebra.

open aff_fr
open aff_lib
universes u 
variables 
    (K : Type u)
    (n : ℕ )
    [inhabited K]
    [field K]
    (fr1 : affine_coord_frame K n) 
    (fr2 : affine_coord_frame K n) 
    (cv1 cv2 : aff_coord_vec K n fr1) 
    (cp1 cp2 : aff_coord_pt  K n fr2)

/-

def affine_coord_frame.build_path
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    :  affine_coord_frame K n → 
        list (affine_tuple_coord_frame K n)
| (affine_coord_frame.tuple b) := [b]
| (affine_coord_frame.derived o b p f) := 
    ⟨o,b,p⟩::(affine_coord_frame.build_path f)

def affine_coord_space.find_transform_path
    {K : Type v}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
    (from_sp : affine_coord_space K n fr1)
    {fr2 : affine_coord_frame K n}
    (to_sp : affine_coord_space K n fr2)
    : transform_path
    := ⟨affine_coord_frame.build_path fr1, 
    affine_coord_frame.build_path fr2⟩

-/
attribute [reducible]
abbreviation square_matrix
    (K : Type u)
    (n : ℕ)
    [inhabited K] 
    [field K] 
    := matrix (fin n) (fin n ) K
 
attribute [reducible]
abbreviation col_matrix
    (K : Type u)
    (n : ℕ)
    [inhabited K] 
    [field K] 
    := matrix (fin n) (fin 1) K

abbreviation 
    affine_coord_frame_transform 
    := 
    (aff_coord_pt K n fr1) 
    ≃ᵃ[K] 
    (aff_coord_pt K n fr2)

abbreviation
    affine_coord_space_transform
    (sp1 : affine_coord_space K n fr1)
    (sp2 : affine_coord_space K n fr2)
    := 
    affine_coord_frame_transform K n fr1 fr2

def affine_vec_coord_tuple.as_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (v : aff_vec_coord_tuple K n)
    : col_matrix K n
    :=
    λ i one, (@aff_lib.coord_helper K n v.1).nth i

attribute [reducible]
def affine_pt_coord_tuple.as_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (v : aff_pt_coord_tuple K n)
    : col_matrix K n
    :=
    λ i one, (@aff_lib.coord_helper K n v.1).nth i

#check fin 3

attribute [reducible]
def affine_coord_vec.to_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (v : aff_coord_vec K n fr)
    : col_matrix K n
    :=
    affine_vec_coord_tuple.as_matrix v.1
    --λ i one, (@aff_lib.coord_helper K n v.1.1).nth i

attribute [reducible]
def affine_coord_pt.to_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (v : aff_coord_pt K n fr)
    : col_matrix K n
    :=
    affine_pt_coord_tuple.as_matrix v.1
    --λ i one, (@aff_lib.coord_helper K n v.1.1).nth i

attribute [reducible]
def col_matrix.as_list
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (coords : col_matrix K n)
    : list K → ℕ → list K
| l nat.zero := l
| l (nat.succ k) := 
    let upd := (coords ⟨k+1,sorry⟩ 1)::l in
        (col_matrix.as_list upd k)++upd

attribute [reducible]
def affine_coord_pt.from_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_coord_frame K n)
    (coords : col_matrix K n)
    : aff_coord_pt K n fr
    := 
    ⟨⟨[1]++(col_matrix.as_list coords [] n),sorry,sorry⟩⟩

attribute [reducible]
def affine_coord_vec.from_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_coord_frame K n)
    (coords : col_matrix K n)
    : aff_coord_vec K n fr
    := 
    ⟨⟨[0]++(col_matrix.as_list coords [] n),sorry,sorry⟩⟩

--#check 
--(rfl :(matrix (fin n) (fin 1) K) = (col_matrix K n))
   -- (matrix (fin n) (fin 1) K)=(matrix (fin n) (fin 1) K))
/-
instance 
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    : has_lift (aff_coord_pt K n fr)
                (matrix (fin n) (fin 1) K)
    := ⟨affine_coord_pt.as_matrix⟩ 
instance 
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    : has_lift (aff_coord_vec K n fr)
                (matrix (fin n) (fin 1) K)
    := ⟨affine_coord_vec.as_matrix⟩ 
-/
/-
invalid definition, a declaration named 
'matrix.has_lift' has already been declaredL
-/
/-
def affine_coord_frame.get_origin_as_col_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_coord_frame K n)
    : col_matrix K n
    :=
-/
attribute [reducible]
def affine_coord_frame.get_basis_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_coord_frame K n)
    : square_matrix K n
    := 
    λ i j,
    (aff_lib.affine_tuple_vec.get_coords  
    (
        (aff_lib.affine_coord_frame.basis_coords 
            fr) j))
    .nth i


attribute [reducible]
def affine_coord_frame.get_origin_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_coord_frame K n)
    : col_matrix K n
    := 
    affine_pt_coord_tuple.as_matrix
        (aff_lib.affine_coord_frame.origin_coords 
            fr)
--should convert the origin point to a vector beforehand
--by subtracting 0,0,0?
attribute [reducible]
def affine_coord_frame.to_homogeneous_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_coord_frame K n)
    : square_matrix K (n+1)
    := λ i j,
        if i.1 < n+1 ∧ j.1 < n+1 then 
        (affine_coord_frame.get_basis_matrix fr) ⟨i.1,sorry⟩ ⟨j.1,sorry⟩
        else if i.1 < n+1 then 
        (affine_coord_frame.get_origin_matrix fr) ⟨i,sorry⟩ ⟨1,sorry⟩
        else if j.1 < n+1 then
        0
        else 
        1

attribute [reducible]
def affine_coord_vec.to_homogeneous_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (v : aff_coord_vec K n fr)
    : col_matrix K (n+1)
    :=
    λ i,
    if i.1 < n+1 then
    (affine_vec_coord_tuple.as_matrix v.1) ⟨i.1,sorry⟩
    else 1
    --λ i one, (@aff_lib.coord_helper K n v.1.1).nth i

attribute [reducible]
def affine_coord_pt.to_homogeneous_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr : affine_coord_frame K n}
    (v : aff_coord_pt K n fr)
    : col_matrix K (n+1)
    :=
    λ i,
    if i.1 < n+1 then
    (affine_pt_coord_tuple.as_matrix v.1) ⟨i.1,sorry⟩
    else 1
    --λ i one, (@aff_lib.coord_helper K n v.1.1).nth i


attribute [reducible]
def affine_coord_pt.from_homogeneous_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_coord_frame K n)
    (coords : col_matrix K (n+1))
    : aff_coord_pt K n fr
    := 
    ⟨⟨[1]++(col_matrix.as_list coords [] n),sorry,sorry⟩⟩

attribute [reducible]
def affine_coord_vec.from_homogeneous_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_coord_frame K n)
    (coords : col_matrix K (n+1))
    : aff_coord_vec K n fr
    := 
    ⟨⟨[0]++(col_matrix.as_list coords [] n),sorry,sorry⟩⟩

/-
def affine_tuple_coord_frame.to_homogeneous_matrix
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_tuple_coord_frame K n)
    : square_matrix K (n+1)
    := λ i j,
        if i.1 < n+1 ∧ j.1 < n+1 then 
        (affine_coord_frame.get_basis_matrix fr) ⟨i.1,sorry⟩ ⟨j.1,sorry⟩
        else if i.1 < n+1 then 
        (affine_coord_frame.get_origin_matrix fr) ⟨i,sorry⟩ ⟨1,sorry⟩
        else if j.1 < n+1 then
        0
        else 
        1
-/
--def fold_transforms
/-
IS THIS IN MATHLIB ALREADY?
NOT matrix.diag_one??
-/
attribute [reducible]
def square_matrix.eye
    (K : Type u)
    (n : ℕ)
    [inhabited K] 
    [field K] 
    : square_matrix K n
    := 
    λ i j,
    if i = j then 1 else 0
/-
undo coordinates:
(x + B^O)
-/

attribute [reducible]
def affine_coord_frame.fold_homogeneous_transform_list
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    : square_matrix K (n) → list (square_matrix K (n)) → square_matrix K (n)
| tr [] := tr
| tr (h::t) := 
    (affine_coord_frame.fold_homogeneous_transform_list 
        (matrix.mul h tr)
        t)

/-
    (
    ((path.from_.map (λf,aff_fr.affine_coord_frame.tuple f))
        .map affine_coord_frame.to_homogeneous_matrix)
    ++
    (((path.to_.map (λf,aff_fr.affine_coord_frame.tuple f))
        .map affine_coord_frame.to_homogeneous_matrix)
        .map (λh,h⁻¹))
    )
-/
attribute [reducible]
noncomputable def transform_path.flatten
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (path : aff_lib.transform_path K n)
    : list (square_matrix K (n+1))
    := 
    (
    ((path.from_.map (λf,aff_fr.affine_coord_frame.tuple f))
        .map affine_coord_frame.to_homogeneous_matrix)
    ++
    (((path.to_.map (λf,aff_fr.affine_coord_frame.tuple f))
        .map affine_coord_frame.to_homogeneous_matrix)
        .map (λh,h⁻¹))
    )

attribute [reducible]
noncomputable def affine_coord_frame.compute_homogeneous_frame_transform
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (path : aff_lib.transform_path K n)
    : square_matrix K (n+1)
    := 
    affine_coord_frame.fold_homogeneous_transform_list
    (square_matrix.eye K (n+1))
    (transform_path.flatten path)
    --([] : list (square_matrix K (n+1)))

--def affine_coord_space.to_transform
attribute [reducible]
noncomputable def affine_coord_space.build_transform
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
    (from_sp : affine_coord_space K n fr1)
    {fr2 : affine_coord_frame K n}
    (to_sp : affine_coord_space K n fr2)
    : affine_coord_space_transform K n fr1 fr2 from_sp to_sp
    :=let tr := 
        affine_coord_frame.compute_homogeneous_frame_transform
        (affine_coord_space.find_transform_path from_sp to_sp) in
    ⟨
        ⟨
        λ p1 : aff_coord_pt K n fr1,
            affine_coord_pt.from_homogeneous_matrix fr2
                (matrix.mul tr 
                    (affine_coord_pt.to_homogeneous_matrix p1)), 
        λ p2 : aff_coord_pt K n fr2,
            affine_coord_pt.from_homogeneous_matrix fr1
                (matrix.mul tr⁻¹
                    (affine_coord_pt.to_homogeneous_matrix p2)), 
                    sorry,sorry⟩

        ,
        sorry,
        sorry
    ⟩

/-
def affine_coord_frame.to_equiv
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    (fr : affine_coord_frame K n)
    :-/
/-
structure equiv (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : left_inverse inv_fun to_fun)
(right_inv : right_inverse inv_fun to_fun)

structure affine_equiv (k P₁ P₂ : Type*) {V₁ V₂ : Type*} [ring k]
  [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁]
  [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] extends P₁ ≃ P₂ :=
(linear : V₁ ≃ₗ[k] V₂)
(map_vadd' : ∀ (p : P₁) (v : V₁), to_equiv (v +ᵥ p) = linear v +ᵥ to_equiv p)
-/

/-
universes u 
variables 
    (K : Type u)
    (n : ℕ )
    [inhabited K]
    [field K]
    (fr1 : affine_coord_frame K n) 
    (fr2 : affine_coord_frame K n) 
    (cv1 cv2 : aff_coord_vec K n fr1) 
    (cp1 cp2 : aff_coord_pt  K n fr2)

abbreviation
    affine_coord_space_transform
    (sp1 : affine_coord_space K n fr1)
    (sp2 : affine_coord_space K n fr2)
    := 
    affine_coord_frame_transform K n fr1 fr2
-/

notation t1⬝t2 := t1.trans t2
notation t1•t2 := t1.trans t2

variables 
    (fr3 : affine_coord_frame K n)
    (s1 : affine_coord_space K n fr1)
    (s2 : affine_coord_space K n fr2)
    (s3 : affine_coord_space K n fr3)
    (t1 : affine_coord_space_transform K n fr1 fr2 s1 s2)
    (t2 : affine_coord_space_transform K n fr2 fr3 s2 s3)
    (p1 : aff_coord_pt K n fr1)
    (p2 : aff_coord_pt K n fr2)
#check t1⬝t2

#check t1 p1
#check t1 p2

def tran_times_vec 
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
   -- (from_sp : affine_coord_space K n fr1)
    {fr2 : affine_coord_frame K n}
   -- (to_sp : affine_coord_space K n fr2)
   (tr : affine_coord_frame_transform K n fr1 fr2)
   (p : aff_coord_vec K n fr1)
   : aff_coord_vec K n fr2
   := tr (p +ᵥ (⟨pt_zero K n⟩ : aff_coord_pt K n fr1))
        -ᵥ (⟨pt_zero K n⟩ : aff_coord_pt K n fr2)


notation t1⬝t2 := tran_times_vec t1 t2
notation t1⬝t2 := t1.to_equiv t2

def affine_coord_space_transform.domain_frame
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
    {from_sp : affine_coord_space K n fr1}
    {fr2 : affine_coord_frame K n}
    {to_sp : affine_coord_space K n fr2}
    (tr : affine_coord_space_transform K n fr1 fr2 from_sp to_sp)
    := fr1

def affine_coord_space_transform.codomain_frame
    {K : Type u}
    {n : ℕ}
    [inhabited K] 
    [field K] 
    {fr1 : affine_coord_frame K n}
    {from_sp : affine_coord_space K n fr1}
    {fr2 : affine_coord_frame K n}
    {to_sp : affine_coord_space K n fr2}
    (tr : affine_coord_space_transform K n fr1 fr2 from_sp to_sp)
    := fr2