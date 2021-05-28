import linear_algebra.affine_space.basic
import .linear2K


-- affine 1 K spaces

universes u 
variables 
(K : Type u) [ring K] [inhabited K]

/-
Objects
-/

-- 1-D point and vector data types represented as 2D vectors
structure pt extends K × K := (inv : fst = 1)
def mk_pt (k : K) : pt K  := pt.mk 1 rfl
structure vec extends K × K := (inv : fst = 0)
def mk_vec (k : K) : vec K := vec.mk 0 rfl

-- Clean up code
attribute [reducible]
def pt.coords 
    {K : Type u} [ring K] [inhabited K]
    (p : pt K) := p.to_prod.2
attribute [reducible]
def vec.coords 
    {K : Type u} [ring K] [inhabited K]
    (v : vec K)
    := v.to_prod.2


attribute [reducible]
def pt.pf
    {K : Type u} [ring K] [inhabited K]
    (p : pt K) := p.inv
attribute [reducible]
def vec.pf
    {K : Type u} [ring K] [inhabited K]
    (v : vec K)
    := v.inv

variables (v : vec K)

/-
Operations
-/

def mul_vec [has_mul K] (k : K) (v : vec K) : vec K := mk_vec K (k * (v.coords))
def neg_vec  [has_mul K] (v : vec K) : vec K := mk_vec K (-1 * v.coords)
def add_vec_vec [has_add K] (v1 v2 : vec K) : vec K := mk_vec K (v1.coords + v2.coords)
def sub_pt_pt (p1 p2 : pt K) : vec K := mk_vec K (p1.coords - p2.coords)
def add_pt_vec [has_add K] (p : pt K) (v : vec K) : pt K := mk_pt K (p.coords + v.coords)
def add_vec_pt (v : vec K) (p : pt K) : pt K := mk_pt K (p.coords + v.coords)
-- add affine combination operation here 

/-
Constants
-/

def pt_zero   := mk_pt K 0
def vec_zero  := mk_vec K 0
def vec_one   := mk_vec K 1
def std_pt : pt K    := pt_zero K
def std_vec : vec K  := vec_one K


/-
Affine_space API
-/

instance : has_add (vec K) := ⟨ add_vec_vec K ⟩  -- Ick! ⟨λv1 v2, ⟨v1.1, v1.2, v1.to_prod.2 + v2.to_prod.2⟩⟩
instance : has_zero (vec K) := ⟨vec_zero K⟩
instance : has_neg (vec K) := ⟨neg_vec K⟩
instance : add_comm_group (vec K) := sorry
@[ext] def vec_scalar : K → vec K → vec K := mul_vec K
instance : has_scalar K (vec K) := ⟨vec_scalar K⟩
instance : mul_action K (vec K) := ⟨sorry, sorry⟩
instance : distrib_mul_action K (vec K) := ⟨sorry,sorry⟩
instance aff_semimod : semimodule K (vec K) := ⟨sorry, sorry⟩
instance aff_module : module K (vec K) := aff_semimod K
def aff_group_action : vec K → pt K → pt K := add_vec_pt K
def aff_group_sub : pt K → pt K → vec K := sub_pt_pt K
instance : has_vadd (vec K) (pt K) := ⟨aff_group_action K⟩
instance : has_vsub (vec K) (pt K) := ⟨aff_group_sub K⟩
instance : add_action (vec K) (pt K) := ⟨
    aff_group_action K, 
    sorry, 
    sorry⟩
instance : nonempty (pt K) := ⟨pt_zero K⟩
instance aff_torsor : add_torsor (vec K) (pt K) := 
⟨sorry,
sorry,
sorry,
sorry,
sorry,
sorry⟩
open_locale affine
instance : affine_space (vec K) (pt K) := aff_torsor K