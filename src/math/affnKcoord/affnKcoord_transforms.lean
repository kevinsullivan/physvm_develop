import .affnKcoord_affinespace
import linear_algebra.matrix
import linear_algebra.affine_space.basic

universes u

section implicitK

variables 
{K : Type u} [field K] [inhabited K] 
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} (s : spc K f)
{dim2 : nat } {id_vec2 : fin dim2 → nat} {f2 : fm K dim2 id_vec2} (s2 : spc K f2)

/-
Andrew 6/27
Had to move this in here - need to wait until the proof that vectr s is an add_comm_group to define this

Also Andrew 6/27 - This should get split into two files, a function library and what is most relevant to the transform
-/


structure vectr_basis := 
    (basis_vectrs : fin dim → vectr s)
    (basis_independent : linear_independent K basis_vectrs)
    (basis_spans : submodule.span K (set.range basis_vectrs))
        

instance : has_lift_t (point s) (pt_n K dim) := ⟨λp, p.coords⟩
instance : has_lift_t (vectr s) (vec_n K dim) := ⟨λv, v.coords⟩
instance : has_lift_t (vectr_basis s) (vec_n_basis K dim) := ⟨λvb, ⟨λi, (vb.basis_vectrs i).coords, sorry, sorry⟩⟩
/-
Used to make a frame using framed points and vectors. Simply use their coordinates,
but their underlying frame is noted as the parent of the derived frame
-/
def mk_frame {f : fm K dim id_vec} {s : spc K f}  (p : point s) (v : vectr_basis s) :=
fm.deriv ↑p ↑v f   -- TODO: make sure v ≠ 0 (erasing tyoe info)
                                      -- TODO: snd arg is really a basis for the vs



/-
An affine equivalence is an equivalence, ≃ᵃ[K], 
between affine spaces such that both forward and
inverse maps are affine.

Lean defines it using an equiv for the map and a 
linear_equiv for the linear part in order to allow
affine equivalences with good definitional equalities.
-/

/-
Let raw_tr be the *type* of an affine equivalence
between abstract affine spaces comprising unframed
(abstract, without coordinates) points and vectors.
-/
abbreviation raw_tr := (pt_n K dim) ≃ᵃ[K] (pt_n K dim)

/-
Structure simply encapsulating an affine transform from 
points between two affine coordinate spaces, s1 and s2.
-/
structure fm_tr 
    {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} 
    (s1 : spc K f1) (s2 : spc K f2) extends (point s1) ≃ᵃ[K] (point s2)

/-
Inverse

KEVIN: Explain, or remove, the .1 notation here. Use identifiers when possible.
-/
def fm_tr.symm  {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} 
    {s1 : spc K f1} {s2 : spc K f2} (ftr : fm_tr s1 s2) : fm_tr s2 s1 :=
    ⟨ftr.1.symm⟩

/-
Composition
-/
def fm_tr.trans  {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} {f3 :  fm K dim id_vec} 
    {s1 : spc K f1} {s2 : spc K f2} {s3 : spc K f3} (ftr : fm_tr s1 s2) : fm_tr s2 s3 → fm_tr s1 s3 :=
    λftr_, ⟨ftr.1.trans ftr_.1⟩

/-
Convert a (our) basis (fin dim → pt_n K dim) to a Lean matrix
-/
def vec_n_basis.to_matrix {K : Type u} [field K] [inhabited K]  {dim : ℕ} (ftok : vec_n_basis K dim) : matrix (fin dim) (fin dim) K :=
    λ i j,
    ((ftok.basis_vecs j) i).coord

def vectr_basis.to_matrix {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} {s : spc K f}  (ftok : vectr_basis s) : matrix (fin dim) (fin dim) K :=
    (↑ftok : vec_n_basis K dim).to_matrix
/-
Convert a frame to a homogeneous matrix. The first column is a 1 + the point coordinates,
The other columns are a 0 + the vectr coordinates
-/
def fm.to_homogeneous_matrix {K : Type u} [field K] [inhabited K] 
{dim : nat} {id_vec : fin dim → nat }(f_ : fm K dim id_vec) : matrix (fin (dim + 1)) (fin (dim + 1)) K
    := 
    if gtz:dim > 0 then
    λ i j, 
    if i=0 ∧ j=0 then 1 
    else if i=0 then 0
    else if j = 0 then (f_.origin ⟨i.1-1, begin
        have h₀ : i.val < dim + 1 := i.2,
        cases dim with dim',
        dsimp only [gt] at gtz,
        have h := nat.not_lt_zero 0 gtz,
        contradiction,
        cases i.1 with i',
        simp only [nat.succ_pos'],
        have h₁ : i'.succ.succ ≤ dim'.succ + 1 := begin
            simp only [has_lt.lt, nat.lt] at h₀,
            simp only [has_le.le],
            exact h₀
        end,
        have h₂ : dim'.succ + 1 = dim'.succ.succ := by simp only [eq_self_iff_true],
        rw h₂ at h₁,
        have h₃ : i'.succ ≤ dim'.succ := nat.le_of_succ_le_succ h₁,
        have h₄ : (i'.succ - 1).succ = i'.succ := by simp only [nat.succ_sub_succ_eq_sub, nat.sub_zero],
        simp only
        
        
        
             [has_le.le] at h₃,
        simp only [has_lt.lt, nat.lt],
        rw h₄,
        exact h₃
    end⟩).coord
    else (f_.basis.basis_vecs ⟨i.1-1,begin
        have h₀ : i.val < dim + 1 := i.2,
        cases dim with dim',
        dsimp only [gt] at gtz,
        have h := nat.not_lt_zero 0 gtz,
        contradiction,
        cases i.1 with i',
        simp only [nat.succ_pos'],
        have h₁ : i'.succ.succ ≤ dim'.succ + 1 := begin
            simp only [has_lt.lt, nat.lt] at h₀,
            simp only [has_le.le],
            exact h₀
        end,
        have h₂ : dim'.succ + 1 = dim'.succ.succ := by simp only [eq_self_iff_true],
        rw h₂ at h₁,
        have h₃ : i'.succ ≤ dim'.succ := nat.le_of_succ_le_succ h₁,
        have h₄ : (i'.succ - 1).succ = i'.succ := by simp only [nat.succ_sub_succ_eq_sub, nat.sub_zero],
        simp only [has_le.le] at h₃,
        simp only [has_lt.lt, nat.lt],
        rw h₄,
        exact h₃
    end⟩ ⟨j.1-1, begin
        have h₀ : j.val < dim + 1 := j.2,
        cases dim with dim',
        dsimp only [gt] at gtz,
        have h := nat.not_lt_zero 0 gtz,
        contradiction,
        cases j.1 with j',
        simp only [nat.succ_pos'],
        have h₁ : j'.succ.succ ≤ dim'.succ + 1 := begin
            simp only [has_lt.lt, nat.lt] at h₀,
            simp only [has_le.le],
            exact h₀
        end,
        have h₂ : dim'.succ + 1 = dim'.succ.succ := by simp only [eq_self_iff_true],
        rw h₂ at h₁,
        have h₃ : j'.succ ≤ dim'.succ := nat.le_of_succ_le_succ h₁,
        have h₄ : (j'.succ - 1).succ = j'.succ := by simp only [nat.succ_sub_succ_eq_sub, nat.sub_zero],
        simp only [has_le.le] at h₃,
        simp only [has_lt.lt, nat.lt],
        rw h₄,
        exact h₃
    end⟩).coord
    else
    λ i j, 1

/-
Convert a point into a "lean vector", with 1 at the top followed by the point's coordinates
-/
def point.to_homogeneous_coords {K : Type u} [field K] [inhabited K] 
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} {s : spc K f}(p : point s) : fin (dim+1) → K
    := 
    if dim = 0 then λi, 1 else
    λi,
    if eqz:i=0 then 1
    else (p.coords ⟨i.1-1, begin
        have h₀ := i.2,
        cases dim with dim',
        {
            simp only [zero_add] at h₀,
            cases i.val with i',
            {
                have h₁ : i = 0 := by simp only [eq_iff_true_of_subsingleton],
                contradiction,
            },
            {
                have h₁ : i'.succ + 1 ≤ 1 := begin
                    dsimp only [has_lt.lt, nat.lt] at h₀,
                    dsimp only [has_le.le],
                    exact h₀,
                end,
                have h₂ := (add_le_add_iff_right 1).1 h₁,
                have h₃ := nat.not_succ_le_zero i',
                contradiction,
            }
        },
        cases i.1 with i',
        simp only [nat.succ_pos'],
        have h₁ : i'.succ.succ ≤ dim'.succ + 1 := begin
            simp only [has_lt.lt, nat.lt] at h₀,
            simp only [has_le.le],
            exact h₀
        end,
        have h₂ : dim'.succ + 1 = dim'.succ.succ := by simp only [eq_self_iff_true],
        rw h₂ at h₁,
        have h₃ : i'.succ ≤ dim'.succ := nat.le_of_succ_le_succ h₁,
        have h₄ : (i'.succ - 1).succ = i'.succ := by simp only [nat.succ_sub_succ_eq_sub, nat.sub_zero],
        simp only [has_le.le] at h₃,
        simp only [has_lt.lt, nat.lt],
        rw h₄,
        exact h₃,
    end⟩).coord


/-
Convert a vector into a "lean vector", with 0 at the top followed by the vector's coordinates
-/
def vectr.to_homogeneous_coords {K : Type u} [field K] [inhabited K] 
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} {s : spc K f}(v : vectr s) : fin (dim+1) → K
    := 
    if dim = 0 then λi, 0 else
    λi,
    if eqz:i=0 then 0
    else (v.coords ⟨i.1-1, begin
        have h₀ := i.2,
        cases dim with dim',
        {
            simp only [zero_add] at h₀,
            cases i.val with i',
            {
                have h₁ : i = 0 := by simp only [eq_iff_true_of_subsingleton],
                contradiction,
            },
            {
                have h₁ : i'.succ + 1 ≤ 1 := begin
                    dsimp only [has_lt.lt, nat.lt] at h₀,
                    dsimp only [has_le.le],
                    exact h₀,
                end,
                have h₂ := (add_le_add_iff_right 1).1 h₁,
                have h₃ := nat.not_succ_le_zero i',
                contradiction,
            }
        },
        cases i.1 with i',
        simp only [nat.succ_pos'],
        have h₁ : i'.succ.succ ≤ dim'.succ + 1 := begin
            simp only [has_lt.lt, nat.lt] at h₀,
            simp only [has_le.le],
            exact h₀
        end,
        have h₂ : dim'.succ + 1 = dim'.succ.succ := by simp only [eq_self_iff_true],
        rw h₂ at h₁,
        have h₃ : i'.succ ≤ dim'.succ := nat.le_of_succ_le_succ h₁,
        have h₄ : (i'.succ - 1).succ = i'.succ := by simp only [nat.succ_sub_succ_eq_sub, nat.sub_zero],
        simp only [has_le.le] at h₃,
        simp only [has_lt.lt, nat.lt],
        rw h₄,
        exact h₃,
    end⟩).coord

/-
Convert an unframed point into a homogeneous lean vector (1 at the top)
-/
def pt_n.to_homogeneous_coords {K : Type u} [field K] [inhabited K]  {dim : ℕ} (p : pt_n K dim) : fin (dim+1) → K
    := 
    if dim = 0 then λi, 1 else
    λi, if eqz:i=0 then 1 
    else (p ⟨i.1-1, begin
        have h₀ := i.2,
        cases dim with dim',
        {
            simp only [zero_add] at h₀,
            cases i.val with i',
            {
                have h₁ : i = 0 := by simp only [eq_iff_true_of_subsingleton],
                contradiction,
            },
            {
                have h₁ : i'.succ + 1 ≤ 1 := begin
                    dsimp only [has_lt.lt, nat.lt] at h₀,
                    dsimp only [has_le.le],
                    exact h₀,
                end,
                have h₂ := (add_le_add_iff_right 1).1 h₁,
                have h₃ := nat.not_succ_le_zero i',
                contradiction,
            }
        },
        cases i.1 with i',
        simp only [nat.succ_pos'],
        have h₁ : i'.succ.succ ≤ dim'.succ + 1 := begin
            simp only [has_lt.lt, nat.lt] at h₀,
            simp only [has_le.le],
            exact h₀
        end,
        have h₂ : dim'.succ + 1 = dim'.succ.succ := by simp only [eq_self_iff_true],
        rw h₂ at h₁,
        have h₃ : i'.succ ≤ dim'.succ := nat.le_of_succ_le_succ h₁,
        have h₄ : (i'.succ - 1).succ = i'.succ := by simp only [nat.succ_sub_succ_eq_sub, nat.sub_zero],
        simp only [has_le.le] at h₃,
        simp only [has_lt.lt, nat.lt],
        rw h₄,
        exact h₃,
    end⟩).coord

/-
Convert an unframed vector into a homogeneous lean vector (0 at the top)
-/
def vec_n.to_homogeneous_coords {K : Type u} [field K] [inhabited K]  {dim : ℕ} (v : vec_n K dim) : fin (dim+1) → K
    :=
    if dim = 0 then λi, 0 else
    λi, if eqz:i=0 then 0 
    else (v ⟨i.1-1, begin
        have h₀ := i.2,
        cases dim with dim',
        {
            simp only [zero_add] at h₀,
            cases i.val with i',
            {
                have h₁ : i = 0 := by simp only [eq_iff_true_of_subsingleton],
                contradiction,
            },
            {
                have h₁ : i'.succ + 1 ≤ 1 := begin
                    dsimp only [has_lt.lt, nat.lt] at h₀,
                    dsimp only [has_le.le],
                    exact h₀,
                end,
                have h₂ := (add_le_add_iff_right 1).1 h₁,
                have h₃ := nat.not_succ_le_zero i',
                contradiction,
            }
        },
        cases i.1 with i',
        simp only [nat.succ_pos'],
        have h₁ : i'.succ.succ ≤ dim'.succ + 1 := begin
            simp only [has_lt.lt, nat.lt] at h₀,
            simp only [has_le.le],
            exact h₀
        end,
        have h₂ : dim'.succ + 1 = dim'.succ.succ := by simp only [eq_self_iff_true],
        rw h₂ at h₁,
        have h₃ : i'.succ ≤ dim'.succ := nat.le_of_succ_le_succ h₁,
        have h₄ : (i'.succ - 1).succ = i'.succ := by simp only [nat.succ_sub_succ_eq_sub, nat.sub_zero],
        simp only [has_le.le] at h₃,
        simp only [has_lt.lt, nat.lt],
        rw h₄,
        exact h₃,
    end⟩).coord

/-
Convert a point into a "lean vector", with 1 at the top followed by the point's coordinates
-/
def point.to_coords {K : Type u} [field K] [inhabited K] 
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} {s : spc K f}(p : point s) : fin (dim) → K
    := 
    λi,
    (p.coords ⟨i.1, i.2⟩).coord


/-
Convert a vector into a "lean vector", with 0 at the top followed by the vector's coordinates
-/
def vectr.to_coords {K : Type u} [field K] [inhabited K] 
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} {s : spc K f}(v : vectr s) : fin (dim) → K
    := 
    λi,
    (v.coords ⟨i.1, i.2⟩).coord

/-
Convert an unframed point into a homogeneous lean vector (1 at the top)
-/
def pt_n.to_coords {K : Type u} [field K] [inhabited K]  {dim : ℕ} (p : pt_n K dim) : fin (dim) → K
    := 
    λi, (p ⟨i.1, i.2⟩).coord

/-
Convert an unframed vector into a homogeneous lean vector (0 at the top)
-/
def vec_n.to_coords {K : Type u} [field K] [inhabited K]  {dim : ℕ} (v : vec_n K dim) : fin (dim) → K
    :=
    λi, (v ⟨i.1, i.2⟩).coord
/-
Convert from a lean vector (with 1 at the top) back into an unframed point in our representation 
-/
def mk_pt_n_from_homogeneous_coords {K : Type u} [field K] [inhabited K]  {dim : ℕ} (coords_:fin (dim+1) → K) : pt_n K dim
    := 
    if gtz:dim>0 then
    λi, mk_pt K (coords_ ⟨i.1+1,begin
        have h₀ : i.val < dim := i.2,
        simp only [has_lt.lt, nat.lt] at h₀ ⊢,
        exact nat.succ_le_succ h₀,
    end⟩)
    else 
    λi, mk_pt K 0
/-
Convert from a lean vector (with 0 at the top) back into an unframed vector in our representation 
-/
def mk_vec_n_from_homogeneous_coords  {K : Type u} [field K] [inhabited K]  {dim : ℕ} (coords_:fin (dim+1) → K) : vec_n K dim
    :=
    if gtz:dim>0 then
    λi, mk_vec K (coords_ ⟨i.1+1,begin
        have h₀ : i.val < dim := i.2,
        simp only [has_lt.lt, nat.lt] at h₀ ⊢,
        exact nat.succ_le_succ h₀,
    end⟩)
    else 
    λi, mk_vec K 0


def mk_point_from_homogeneous_coords {K : Type u} [field K] [inhabited K] 
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} {s : spc K f} (coords_:fin (dim+1) → K) : point s
    := 
    if gtz:dim>0 then
    ⟨λi, mk_pt K (coords_ ⟨i.1+1,begin
        have h₀ : i.val < dim := i.2,
        simp only [has_lt.lt, nat.lt] at h₀ ⊢,
        exact nat.succ_le_succ h₀,
    end⟩)⟩
    else 
    ⟨λi, mk_pt K 0⟩
/-
Convert from a lean vector (with 0 at the top) back into an unframed vector in our representation 
-/
def mk_vectr_from_homogeneous_coords {K : Type u} [field K] [inhabited K] 
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} {s : spc K f} (coords_:fin (dim+1) → K) : vectr s
    :=
    if gtz:dim>0 then
    ⟨λi, mk_vec K (coords_ ⟨i.1+1, begin
        have h₀ : i.val < dim := i.2,
        simp only [has_lt.lt, nat.lt] at h₀ ⊢,
        exact nat.succ_le_succ h₀,
    end⟩)⟩
    else 
    ⟨λi, mk_vec K 0⟩
/-
Convert from a lean vector back into an unframed point in our representation 
-/
def mk_pt_n_from_coords {K : Type u} [field K] [inhabited K] {dim : ℕ} (coords_:fin (dim) → K) : pt_n K dim
    := 
    λi, mk_pt K (coords_ ⟨i.1, i.2⟩)
/-
Convert from a lean vector (with 0 at the top) back into an unframed vector in our representation 
-/
def mk_vec_n_from_coords {K : Type u} [field K] [inhabited K] {dim : ℕ} (coords_:fin (dim) → K) : vec_n K dim
    :=
    λi, mk_vec K (coords_ ⟨i.1, i.2⟩)


def mk_point_from_coords {K : Type u} [field K] [inhabited K] 
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} {s : spc K f} (coords_:fin (dim) → K) : point s
    := 
    ⟨λi, mk_pt K (coords_ ⟨i.1,i.2⟩)⟩
/-
Convert from a lean vector (with 0 at the top) back into an unframed vector in our representation 
-/
def mk_vectr_from_coords {K : Type u} [field K] [inhabited K] 
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} {s : spc K f} (coords_:fin (dim) → K) : vectr s
    :=
    ⟨λi, mk_vec K (coords_ ⟨i.1,i.2⟩)⟩
/-
Exploit's cramer's rule to form a computable inverse for a given matrix.
Used in computing transforms
-/
def matrix.cramer_inverse 
    {dim : ℕ} {K : Type u} [inhabited K] [field K] : matrix (fin dim) (fin dim) K →
    matrix (fin dim) (fin dim) K := 
    λm,
    λ i j,
    if dgz:dim>0 then 
    let detm := m.cramer (λi, m i ⟨0, begin
        dsimp only [gt] at dgz,
        exact dgz
    end⟩) ⟨0, begin
        dsimp only [gt] at dgz,
        exact dgz
    end⟩ in
    let colj : fin dim → K := λi, if i = j then 1 else 0 in
    (m.cramer colj i)/detm
    else 0

/-
Helper function for general transforms.
Given a Frame A, this will compute a transform from a vector or point expressed in A,
to the Parent Frame of A, B, and recursively call itself until B is the standard frame. 
Thus, it computes a transform from A to the standard frame. Note that the inverse of this transform is from the standard frame to A.
This is used to crawl through a "Frame Tree" to compute a transform between any two arbitrary frames that
are not necessarily connected.

In the function, note that we match on the frame, and that if it is frame.base, 
it is simply the identity transform since the standard frame is its own parent.
In the deriv case, we turn the coordinates of the frame into a homogeneous matrix
and simply use the homogeneous matrix as the transform.
-/

def to_base_helper' :  fm K dim id_vec → @raw_tr K _ _ dim
| (fm.base dim id_vec) := ⟨
            ⟨   /-base case -/
                (λ p, p),
                (λ p, p),
                begin
                    unfold function.left_inverse,
                    intros,
                    simp *
                end,
                begin
                    unfold function.right_inverse function.left_inverse,
                    intros,
                    simp *
                end
            ⟩,
            ⟨
                (λ v, v),
                begin
                    intros, simp*
                end,
               -- (λ v, ⟨v.coords⟩),
                begin
                    intros, simp *
                end,
                (λ v, v),
                begin
                    unfold function.left_inverse,
                    intros, simp *
                end,
                begin
                    unfold function.left_inverse function.right_inverse,
                    intros, simp *
                end,
            ⟩,
            begin
                simp *,
                --admit   -- TODO: What's this?
            end
        ⟩
| (fm.deriv origin basis parent) := (⟨
            ⟨/-transform from current->parent-/
                (λ (p : pt_n K dim),
                mk_pt_n_from_homogeneous_coords 
                (((fm.deriv origin basis parent).to_homogeneous_matrix.mul_vec p.to_homogeneous_coords) : fin (dim + 1) → K)
                : pt_n K dim → pt_n K dim),
                (λ (p : pt_n K dim),
                mk_pt_n_from_homogeneous_coords 
                ((((fm.deriv origin basis parent).to_homogeneous_matrix.cramer_inverse).mul_vec p.to_homogeneous_coords) : fin (dim + 1) → K)
                : pt_n K dim → pt_n K dim),
                sorry,
                sorry,
            ⟩,
            ⟨
                λv, v,
                by {intros, refl},
                by {intros, refl},
                by {intro h, exact h},
                by {dsimp only [function.left_inverse], intros, refl},
                by {dsimp only [function.right_inverse, function.left_inverse], intros, refl}
            ⟩,
            sorry /-invert to parent->current and append to current->base-/
⟩ : @raw_tr K _ _ dim).trans (to_base_helper' parent)

/-
Extension method to get a transform from a space to the base (standard) frame 
(essentially a transform from a frame to the standard frame, since spc is mostly 
a wrapper around a frame)
-/
def spc.to_base {f1 :  fm K dim id_vec} (s1 : spc K f1) : @raw_tr K _ _ dim := to_base_helper' f1

/-
Our general function which computes a transform from one space to another.
First computes the transform from the SOURCE space down to the standard space, 
TrA, and then computes the transform of the TARGET space down to the standard
space TrB, and composes TrA with the INVERSE of TrB. This yields a transform
from A to B.
-/
def spc.fm_tr {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} (s1 : spc K f1) : Π (s2 : spc K f2),
    fm_tr s1 s2 
    := 
    λ s2,
    ⟨
    let rawtr : @raw_tr K _ _ dim := s1.to_base.trans s2.to_base.symm in
                ⟨
            ⟨
                (λ p : point _, (⟨(rawtr p.1 : pt_n K dim)⟩ : point _)),
                (λ p : point _, (⟨(rawtr p.1 : pt_n K dim)⟩ : point _)),
                sorry,
                sorry
            ⟩,
            ⟨
                (λv : vectr _, (⟨(rawtr.linear v.1 : vec_n K dim)⟩ : vectr _)),
                sorry,
               -- (λ v, ⟨v.coords⟩),
                sorry,
                (λv : vectr _, (⟨(rawtr.linear v.1 : vec_n K dim)⟩ : vectr _)),
                sorry,
                sorry
            ⟩,
            sorry
        ⟩
    ⟩

/-
Extension method for a computed transform which allows you to transform a point 
between two coordinate spaces.
-/

def fm_tr.transform_point  
    {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} 
    {s1 : spc K f1} {s2 : spc K f2} (tr:fm_tr s1 s2 ) 
    : point s1 → point s2 :=
    λp,
    tr.to_equiv p

/-
Extension method for a computed transform which allows you to transform a vectr 
between two coordinate spaces. Note there is some magic here because lean "affine 
transforms" only allow you to transform between points.
-/

def fm_tr.transform_vectr  
    {f1 :  fm K dim id_vec} {f2 :  fm K dim id_vec} 
    {s1 : spc K f1} {s2 : spc K f2} (tr:fm_tr s1 s2 ) 
    : vectr s1 → vectr s2 :=
    λv,
    let as_pt : point s1 := ⟨λi, mk_pt K (v.coords i).coord⟩ in
    let tr_pt := (tr.to_equiv as_pt) in
    ⟨λi, mk_vec K (tr_pt.coords i).coord⟩

/-
Requested Dr Sullivan on 6/16.
Simple sugared helper methods to express a point/vector in a different 
coordinate space
-/
def point.expressed_in 
    {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} {s : spc K f}  
    {f2: fm K dim id_vec} {s2 : spc K f2} 
    
    (p1 : point s) (s2 : spc K f2) : point s2 :=
    (s.fm_tr s2).transform_point p1

def vectr.expressed_in 
    {dim : ℕ} {id_vec : fin dim → ℕ} {f: fm K dim id_vec} {s : spc K f}  
    {f2: fm K dim id_vec} {s2 : spc K f2} 
    
    (v1 : vectr s) (s2 : spc K f2) : vectr s2 :=
    (s.fm_tr s2).transform_vectr v1

end implicitK