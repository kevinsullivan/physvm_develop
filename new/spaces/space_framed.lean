import .space_unframed

/-
Framed points, vectors, frames
-/

universes u --v w
variables 
(K : Type u) [ring K] [inhabited K] 

-- frames
inductive fm : Type u
| base : fm
| deriv (self : prod (pt K) (vec K)) (parent : fm) : fm

def mk_fm (p : pt K) (v : vec K) (f : fm K): fm K := fm.deriv (p, v) f 
def std_fm : fm K    := fm.base  

structure spc (f : fm K) : Type u 
structure point {f : fm K} (s : spc K f ) extends pt K
structure vectr {f : fm K} (s : spc K f ) extends vec K

def mk_frame {parent : fm K} {s : spc K parent}  (p : point K s) (v : vectr K s) :=
fm.deriv (p.to_pt, v.to_vec) parent   -- make sure v ≠ 0

def mk_point {f : fm K} (s : spc K f ) (k : K) : point K s :=
point.mk (mk_pt K k)  

def mk_vectr {f : fm K} (s : spc K f ) (k : K) : vectr K s :=
vectr.mk (mk_vec K k)  

def mk_space (f : fm K) :=
  @spc.mk K _ _ f

/-
Operations
-/

/-
/-
Affine space operations
-/
def mul_vectr (k : K) (v : vec K) [has_mul K] : vec K := mk_vec K (k * v.coord)
def neg_vectr (k : K) (v : vec K) [has_mul K] : vec K := mk_vec K (-1 * v.coord)
def add_vectr_vectr (k : K) (v1 v2 : vec K) [has_add K] : vec K := mk_vec K (v1.coord + v2.coord)
def add_point_vectr (k : K) (p : pt K) (v : vec K) [has_add K] : pt K := mk_pt K (p.coord + v.coord)
def add_vectr_point (v : vec K) (p : pt K) : pt K := mk_pt K (p.coord + v.coord)
def sub_pt_pt (p1 p2 : pt K) : vec K := mk_vec K (p2.coord - p1.coord)



/-
 Make it an affine space
-/

/-
Instantiate affine_space typeclass 
-/
open_locale affine
section old_structure_cmd
set_option old_structure_cmd true

instance : inhabited (point K) := ⟨ pt_zero K ⟩ 
instance : has_zero (vectr K) := ⟨ vec_zero K ⟩ 
instance : has_vadd (vectr K) (point K) := ⟨ add_vectr_point K ⟩ 
instance : has_vsub (vectr K) (point K) := ⟨ sub_pt_pt K ⟩ 
instance : add_comm_group (vectr K) := sorry

/-
Lemmas needed to prove we've got an affine space
-/
lemma aff_zero_sadd : ∀ p : pt K, (0 : vec K) +ᵥ p = p := sorry
lemma aff_add_sadd: ∀ g1 g2 : vec K, ∀ p : pt K, g1 +ᵥ (g2 +ᵥ p) = g1 + g2 +ᵥ p := sorry   -- problem here
lemma aff_vsub_vadd : ∀ a b : pt K, (a -ᵥ b) +ᵥ b = a := sorry
lemma aff_vadd_vsub : ∀ (x : vec K) (a : pt K), x +ᵥ a -ᵥ a = x := sorry

instance : add_action (vec K) (pt K) := 
⟨
add_vectr_point K,    -- aff_group_action
aff_zero_sadd K, 
aff_add_sadd K
⟩

instance aff_torsor : add_torsor (vec K) (pt K) := 
⟨add_vectr_point K, 
aff_zero_sadd K,
aff_add_sadd K,
sub_pt_pt K,
aff_vsub_vadd K, 
aff_vadd_vsub K
⟩

instance my_affine_space : affine_space (vec K) (pt K) :=  
aff_torsor K 

end old_structure_cmd
-/

