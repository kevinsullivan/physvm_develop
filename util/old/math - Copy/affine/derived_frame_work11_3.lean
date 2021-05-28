
inductive fr_type : Type
| base {dim : ℕ} (fr : affine_frame (aff_pt_coord_tuple ℝ dim) ℝ (aff_vec_coord_tuple ℝ dim) (fin dim)) : fr_type 
| derived  {dim : ℕ} (fr : affine_frame (pt_with_frame ℝ dim) ℝ (aff_vec_coord_tuple ℝ dim) (fin dim)) : fr_type 


def get_vecl : ℕ → list ℝ
| (nat.succ n) := (0:ℝ) :: get_vecl n
| 0 := []

def get_e_i (dim : ℕ) : list ℝ → ℕ → list ℝ
| l (nat.succ n) := if nat.succ n = dim then (1:ℝ) :: l else (0:ℝ) :: l
| l (nat.zero) := l

def get_zero_pt (dim : ℕ) : aff_pt_coord_tuple ℝ dim := ⟨get_vecl dim, sorry, sorry⟩

def vector_copy_helper {dim : ℕ} : vector ℝ dim → ℕ → list ℝ → list ℝ 
| v (nat.succ n) l := [(v.nth (⟨n,sorry⟩ : fin dim))]++(vector_copy_helper v n l)
| v (nat.zero) l := l
--| v idx l := if idx = dim then (1:ℝ)::l else (vector_copy_helper v idx-1 l)++[(v.nth (⟨idx,sorry⟩ : fin dim))]
def vector_to_vec_list {dim : ℕ} : vector ℝ dim → list ℝ
| v := 0::(vector_copy_helper v.reverse dim []).reverse

def vector_to_pt_list {dim : ℕ} : vector ℝ dim → list ℝ
| v := 1::(vector_copy_helper v.reverse dim []).reverse
--| v idx l := if idx = dim then (1:ℝ)::l else (vector_to_pt_list v idx l)++[(v.nth (⟨idx,sorry⟩ : fin dim))]

def vector_to_vec {dim : ℕ} : vector ℝ dim → aff_vec_coord_tuple ℝ dim 
    := λv, ⟨vector_to_vec_list v, sorry, sorry⟩

def vector_to_pt {dim : ℕ} : vector ℝ dim → aff_pt_coord_tuple ℝ dim 
    := λv, ⟨vector_to_pt_list v, sorry, sorry⟩

def get_basis (dim : ℕ) : fin dim → aff_vec_coord_tuple ℝ dim :=
    λ (n : fin dim), ⟨get_e_i dim ([] : list ℝ) dim, sorry, sorry⟩



noncomputable def get_standard_frame_on_real_coordinate_space {X : Type*} {V : Type*}  {dim : ℕ}
    [add_comm_group V] [module ℝ V] [affine_space V X]
    (fr : affine_frame  X ℝ V (fin dim)) 
        (sp : real_affine_coordinate_space fr) : 
    affine_frame  (pt_with_frame ℝ dim) ℝ (aff_vec_coord_tuple ℝ dim) (fin dim) :=
    --⟨(get_zero_pt dim) ,(get_basis dim) ,sorry⟩ 
    aff_basis.std_frame ℝ dim--aff_basis.std_basis (aff_pt_coord_tuple ℝ dim) dim ℝ (aff_vec_coord_tuple ℝ dim) (fin dim) 


noncomputable def real_affine_space.get_standard_frame {X : Type*} {V : Type*}
    [add_comm_group V] [module ℝ V] [affine_space V X]{dim : ℕ} {f : real_affine_frame X V dim} 
    (sp : real_affine_coordinate_space f)
    
    := get_standard_frame_on_Rn dim --⟨get_zero_pt dim, get_basis dim, sorry⟩

  
def to_coordinatized_affine_space (n : ℕ) (fr : real_affine_frame n) : real_affine_coordinate_space fr :=--(get_standard_frame_on_Rn n) := 
    ⟨⟩ 
def to_affine_vector {n : ℕ} (v : vector ℝ n) : real_affine_vector n :=
    vector_to_vec v

def to_affine_point {n : ℕ} (v : vector ℝ n) : real_affine_point n :=
    vector_to_pt v

def to_standard_frame (n : ℕ) : real_affine_frame n :=
    ⟨real_affine_space.get_standard_frame (⟨⟩ : real_affine_space n)⟩

def to_affine_vector_with_frame {n : ℕ} (v : vector ℝ n)
    {fr : real_affine_frame n} 
    (sp : real_affine_coordinate_space fr) :
    real_affine_coordinate_vector n fr :=
    ⟨(vector_to_vec v)⟩


def to_affine_point_with_frame {n : ℕ} (v : vector ℝ n)
    {fr : real_affine_frame n} 
    (sp : real_affine_coordinate_space fr) :
    real_affine_coordinate_point n fr :=
    ⟨(vector_to_pt v)⟩