import .space_unframed
import linear_algebra.affine_space.basic

open_locale affine

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
-- def std_fm : fm K    := fm.base  

structure spc (f : fm K) : Type u
def mk_space (f : fm K) :=
  @spc.mk K _ _ f

structure point {f : fm K} (s : spc K f ) extends pt K
def mk_point {f : fm K} (s : spc K f ) (k : K) : point K s :=
point.mk (mk_pt K k)  

structure vectr {f : fm K} (s : spc K f ) extends vec K
def mk_vectr {f : fm K} (s : spc K f ) (k : K) : vectr K s :=
vectr.mk (mk_vec K k)  

def mk_frame {parent : fm K} {s : spc K parent}  (p : point K s) (v : vectr K s) :=
fm.deriv (p.to_pt, v.to_vec) parent   -- TODO: make sure v ≠ 0

/-
Operations
-/


/-
Affine space operations
-/
def mul_vectr {f : fm K} {s : spc K f } (k : K) (v : vectr K s) : vectr K s := mk_vectr K s (k * v.to_vec.to_prod.2) -- yuck
def neg_vectr {f : fm K} {s : spc K f } (k : K) (v : vectr K s) : vec K := mk_vec K (-1 * v.to_vec.to_prod.2)
def add_vectr_vectr {f : fm K} {s : spc K f } (k : K) (v1 v2 : vectr K s) : vec K := mk_vec K (v1.to_vec.to_prod.2 + v2.to_vec.to_prod.2)
def add_point_vectr {f : fm K} {s : spc K f } (k : K) (p : point K s) (v : vectr K s) : point K s := mk_point K s (p.to_pt.to_prod.2 + v.to_vec.to_prod.2)
def add_vectr_point {f : fm K} {s : spc K f } (v : vectr K s) (p : point K s) : point K s := mk_point K s (v.to_vec.to_prod.2 + p.to_pt.to_prod.2)
def sub_point_point {f : fm K} {s : spc K f } (p1 p2 : point K s) : vectr K s := mk_vectr K s (p2.to_pt.to_prod.2 - p1.to_pt.to_prod.2)

/-

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

variables {f : fm K} { s : spc K f}

variable v : vectr K s
#check v        -- v : vectr K s
#check v.1      -- v.to_vec : vec K
#check v.1.1    -- v.to_vec.isPt : K
#check v.1.2    -- v.to_vec.inv : v.to_vec.isPt = 0
#check vec

/-
The following notation is uninterpretable:
λv1 v2, ⟨⟨v1.1.1,v1.1.2,v1.coord + v2.coord⟩⟩
Please leave explanation here of what this 
term is/means. Use identifer rather than
numeric projections with good names.

FIX THIS CODE. IT'S TERRIBLE. See unframed file for template.
-/
instance : has_add (vectr K s) := ⟨λv1 v2, ⟨⟨v1.1.1,v1.1.2,v1.coord + v2.coord⟩⟩⟩
instance : has_zero (vectr K s) := ⟨⟨vec_zero K⟩⟩
instance : has_neg (vectr K s) := ⟨λv, ⟨⟨v.1.1,v.1.2,-v.1.3⟩⟩⟩
/-
Keep this copy.
instance : has_add (vectr K s) := ⟨λv1 v2, ⟨⟨v1.1.1,v1.1.2,v1.coord + v2.coord⟩⟩⟩
instance : has_zero (vectr K s) := ⟨⟨vec_zero K⟩⟩
instance : has_neg (vectr K s) := ⟨λv, ⟨⟨v.1.1,v.1.2,-v.1.3⟩⟩⟩-/

/-! ### Type class instance for abelian group -/
instance aff_comm_group_framed : add_comm_group (vectr K s) :=
sorry


/-! ### Scalar action -/


@[ext]
def vec_scalar_framed : K → vectr K s → vectr K s :=
    λ a x, ⟨⟨x.1.1,x.1.2,a*x.1.3⟩⟩

instance : has_scalar K (vectr K s) := ⟨vec_scalar_framed K⟩

instance : mul_action K (vectr K s) := ⟨sorry, sorry⟩

instance : distrib_mul_action K (vectr K s) := ⟨sorry,sorry⟩

instance aff_semimod_framed : semimodule K (vectr K s) := ⟨sorry, sorry⟩

instance aff_module_framed : module K (vectr K s) := aff_semimod_framed K

/-! ### group action of aff_vec_coord_tuple on aff_pt_coord_tuple -/


def aff_group_action_framed : vectr K s → point K s → point K s :=
    λ x y, ⟨⟨y.1.1,y.1.2,x.1.3+y.1.3⟩⟩


def aff_group_sub_framed : point K s → point K s → vectr K s :=
    λ x y, ⟨⟨x.1.1-y.1.1,sorry,x.1.3-y.1.3⟩⟩

#check add_action

instance : has_vadd (vectr K s) (point K s) := ⟨aff_group_action_framed K⟩

instance : has_vsub (vectr K s) (point K s) := ⟨aff_group_sub_framed K⟩

instance : add_action (vectr K s) (point K s) := ⟨
    aff_group_action_framed K, 
    sorry, 
    sorry⟩


instance : nonempty (point K s) := ⟨⟨pt_zero K⟩⟩

instance aff_torsor_framed : add_torsor (vectr K s) (point K s) := 
⟨sorry,
sorry,
sorry,
sorry,
sorry,
sorry⟩


instance aff_coord_is_framed : 
    affine_space
        (vectr K s) 
        (point K s) := 
    aff_torsor_framed K

