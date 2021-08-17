import ..aff1Kcoord.aff1K
import tactic.linarith
import linear_algebra.std_basis

universes u 
variables 
(K : Type u) 
[field K]
[inhabited K]
(n : ℕ)

open_locale affine

abbreviation pt_n := fin (n) → pt K
abbreviation vec_n := fin (n) → vec K

def mk_pt_n (vals : vector K n) : pt_n K n := 
  λi, mk_pt K (vals.nth i)

def mk_vec_n (vals : vector K n) : vec_n K n := 
  λi, mk_vec K (vals.nth i)

def pt_n.coords {K : Type u}
[field K]
[inhabited K]
{n : ℕ} (ptn : pt_n K n) : fin n → K :=
  λi, (ptn i).coord

def vec_n.coords {K : Type u}
[field K]
[inhabited K]
{n : ℕ} (vecn : vec_n K n) : fin n → K :=
  λi, (vecn i).coord

#check nat.sub_le_left_iff_le_add
def mk_pt_prod {n1 : ℕ} (p1 : pt_n K n1) {n2 : ℕ} (p2 : pt_n K n2) : pt_n K (n1+n2) := 
  λi, if lt:i.1<n1 then p1 ⟨i.1,begin cc end⟩ else p2 ⟨i.1-n1,begin 
    exact (nat.sub_lt_left_iff_lt_add (by linarith)).elim_right i.2,
  end⟩

def mk_vec_prod {n1 : ℕ} (p1 : pt_n K n1) {n2 : ℕ} (p2 : pt_n K n2) : pt_n K (n1+n2) := 
  λi, if lt:i.1<n1 then p1 ⟨i.1,begin cc end⟩ else p2 ⟨i.1-n1,begin 
    exact (nat.sub_lt_left_iff_lt_add (by linarith)).elim_right i.2,
  end⟩

@[reducible,elab_with_expected_type, simp]
def add_maps {n1 n2 : ℕ} {T : Type u} (m1 : fin n1 → T) (m2 : fin n2 → T) : (fin (n1 + n2) → T) := 
  λi, if lt:i.1 < n1 then m1 ⟨i.1,begin cc end⟩ else m2 ⟨i.1-n1,begin 
    exact (nat.sub_lt_left_iff_lt_add (by linarith)).elim_right i.2,
  end⟩

structure vec_n_basis :=
  (basis_vecs:fin n → vec_n K n)
  (basis_independent : linear_independent K basis_vecs)
  (basis_spans : submodule.span K (set.range basis_vecs) = ⊤)

instance : has_lift_t (vec_n_basis K n) (fin n → vec_n K n) := ⟨λvb, vb.basis_vecs⟩

--done
instance : add_comm_group (vec_n K n) := by apply_instance
instance : affine_space (vec_n K n) (pt_n K n) := by apply_instance

