import linear_algebra.affine_space.basic

universes u 

variables 
(K : Type u) [ring K] [inhabited K]

/-
Frameless points, vectors
-/
structure vec :=
(isPt  : K)
(inv : isPt = (0:K))
(coord : K)

#check vec

structure pt :=
(isPt  : K)
(inv : isPt = (1:K))
(coord : K)

def mk_vec (k : K) : vec K := vec.mk 0 rfl k
def mk_pt (k : K) : pt K  := pt.mk 1 rfl k

/-
Affine space operations
-/
def mul_vec (k : K) (v : vec K) [has_mul K] : vec K := mk_vec K (k * v.coord)
def neg_vec (k : K) (v : vec K) [has_mul K] : vec K := mk_vec K (-1 * v.coord)
def add_vec_vec (k : K) (v1 v2 : vec K) [has_add K] : vec K := mk_vec K (v1.coord + v2.coord)
def add_pt_vec (k : K) (p : pt K) (v : vec K) [has_add K] : pt K := mk_pt K (p.coord + v.coord)
def add_vec_pt (v : vec K) (p : pt K) : pt K := mk_pt K (p.coord + v.coord)
def sub_pt_pt (p1 p2 : pt K) : vec K := mk_vec K (p2.coord - p1.coord)

-- TODO: add affine combination operation here 

/-
One values for pts and vecs 
-/
def pt_zero   := mk_pt K 0
def vec_zero  := mk_vec K 0
def vec_one   := mk_vec K 1
def std_pt : pt K    := pt_zero K
def std_vec : vec K  := vec_one K

/-
Instantiate affine_space typeclass 
-/
open_locale affine
section old_structure_cmd
set_option old_structure_cmd true
/--/
instance : inhabited (pt K) := ⟨ pt_zero K ⟩ 
instance : has_zero (vec K) := ⟨ vec_zero K ⟩ 
instance : has_vadd (vec K) (pt K) := ⟨ add_vec_pt K ⟩ 
instance : has_vsub (vec K) (pt K) := ⟨ sub_pt_pt K ⟩ 
instance : add_comm_group (vec K) := sorry

/-
Lemmas needed to prove we've got an affine space
-/
lemma aff_zero_sadd : ∀ p : pt K, (0 : vec K) +ᵥ p = p := sorry
lemma aff_add_sadd: ∀ g1 g2 : vec K, ∀ p : pt K, g1 +ᵥ (g2 +ᵥ p) = g1 + g2 +ᵥ p := sorry   -- problem here
lemma aff_vsub_vadd : ∀ a b : pt K, (a -ᵥ b) +ᵥ b = a := sorry
lemma aff_vadd_vsub : ∀ (x : vec K) (a : pt K), x +ᵥ a -ᵥ a = x := sorry

instance : add_action (vec K) (pt K) := 
⟨
add_vec_pt K,    -- aff_group_action
aff_zero_sadd K, 
aff_add_sadd K
⟩

instance aff_torsor : add_torsor (vec K) (pt K) := 
⟨add_vec_pt K, 
aff_zero_sadd K,
aff_add_sadd K,
sub_pt_pt K,
aff_vsub_vadd K, 
aff_vadd_vsub K
⟩

instance my_affine_space : affine_space (vec K) (pt K) :=  
aff_torsor K -/

instance : has_add (vec K) := ⟨λv1 v2, ⟨v1.1,v1.2,v1.coord + v2.coord⟩⟩
instance : has_zero (vec K) := ⟨vec_zero K⟩
instance : has_neg (vec K) := ⟨λv, ⟨v.1,v.2,-v.3⟩⟩

/-! ### Type class instance for abelian group -/
instance aff_comm_group : add_comm_group (vec K) :=
sorry


/-! ### Scalar action -/


@[ext]
def vec_scalar : K → vec K → vec K :=
    λ a x, ⟨x.1,x.2,a*x.3⟩

instance : has_scalar K (vec K) := ⟨vec_scalar K⟩

instance : mul_action K (vec K) := ⟨sorry, sorry⟩

instance : distrib_mul_action K (vec K) := ⟨sorry,sorry⟩

instance aff_semimod : semimodule K (vec K) := ⟨sorry, sorry⟩

instance aff_module : module K (vec K) := aff_semimod K

/-! ### group action of aff_vec_coord_tuple on aff_pt_coord_tuple -/


def aff_group_action : vec K → pt K → pt K :=
    λ x y, ⟨y.1,y.2,x.3+y.3⟩


def aff_group_sub : pt K → pt K → vec K :=
    λ x y, ⟨x.1-y.1,sorry,x.3-y.3⟩

#check add_action

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


instance aff_coord_is : 
    affine_space 
        (vec K) 
        (pt K) := 
    aff_torsor K



end old_structure_cmd



