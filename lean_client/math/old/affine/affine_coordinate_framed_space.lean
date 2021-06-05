import linear_algebra.affine_space.basic
import linear_algebra.basis
import .affine_coordinate_space
import data.real.basic



open_locale affine
/-
This file contains
affine_tuple_coord_frame
affine_coord_frame
aff_coord_pt
aff_coord_vec
Also all instances necessary. Missing some proofs 11/20
-/



namespace aff_fr

universes u v w

variables 
    -- (id : ℕ)
    (X : Type u) 
    (K : Type v) 
    (V : Type w) 
    (n : ℕ) 
    (k : K)
    (ι : Type*)
    (s : finset ι) 
    (g : ι → K) 
    (v : ι → V) 
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    [is_basis K v] 

/-
An affine frame comprises an origin point
and a basis for the vector space.
-/
structure affine_tuple_coord_frame
(K : Type w)
(n : ℕ)
[inhabited K]
[field K]  :=
mk ::
    (origin : aff_pt_coord_tuple K n) 
    (basis : (fin n) → aff_vec_coord_tuple K n) 
    (proof_is_basis : is_basis K basis) 

inductive affine_coord_frame
(K : Type w)
(n : ℕ)
[inhabited K]
[field K]
| tuple (base : affine_tuple_coord_frame K n) 
    : affine_coord_frame
| derived 
    (origin : aff_pt_coord_tuple K n) 
    (basis : (fin n) → aff_vec_coord_tuple K n) 
    (proof_is_basis : is_basis K basis) 
    (base : affine_coord_frame)
    : affine_coord_frame

@[ext]
structure aff_coord_pt (fr : affine_coord_frame K n) 
            extends aff_pt_coord_tuple K n :=
   -- (tuple : aff_pt_coord_tuple K n)
   mk ::

@[ext]
structure aff_coord_vec (fr : affine_coord_frame K n) 
            extends aff_vec_coord_tuple K n  :=
   -- (tuple : aff_vec_coord_tuple K n)
   mk ::

variables 
    (fr : affine_coord_frame K n) 
    (cv1 cv2 : aff_coord_vec K n fr) 
    (cp1 cp2 : aff_coord_pt  K n fr)

def pt_zero_coord : aff_coord_pt K n fr := ⟨pt_zero K n⟩
def zero_vector_coord : aff_coord_vec K n fr := ⟨vec_zero K n⟩


/-! ### abelian group operations -/
def vec_add_coord : aff_coord_vec K n fr → aff_coord_vec K n fr → aff_coord_vec K n fr :=
    λ x y, ⟨x.1 + y.1⟩
def vec_zero_coord : aff_coord_vec K n fr := ⟨vec_zero K n⟩
def vec_neg_coord : aff_coord_vec K n fr → aff_coord_vec K n fr
| ⟨x⟩ := ⟨⟨λ m : fin n, -(x.1 m)⟩⟩

/-! ### type class instances for the abelian group operations -/
instance : has_add (aff_coord_vec K n fr) := ⟨vec_add_coord K n fr⟩
instance : has_zero (aff_coord_vec K n fr) := ⟨vec_zero_coord K n fr⟩
instance : has_neg (aff_coord_vec K n fr) := ⟨vec_neg_coord K n fr⟩

-- properties necessary to show aff_vec_coord_tuple K n is an instance of add_comm_group
#print add_comm_group
lemma vec_add_assoc_coord : ∀ x y z : aff_coord_vec K n fr,  x + y + z = x + (y + z) :=
begin
intros,
ext m,
exact add_assoc (x.1.1 m) (y.1.1 m) (z.1.1 m),
end

lemma vec_zero_is_coord : (0 : aff_coord_vec K n fr) = vec_zero_coord K n fr := rfl

lemma vec_zero_add_coord : ∀ x : aff_coord_vec K n fr, 0 + x = x :=
begin
intro x,
ext m,
exact zero_add (x.1.1 m),
end

lemma vec_add_zero_coord : ∀ x : aff_coord_vec K n fr, x + 0 = x :=
begin
intro x,
ext m,
exact add_zero (x.1.1 m),
end

lemma vec_add_left_neg_coord : ∀ x : aff_coord_vec K n fr, -x + x = 0 :=
begin
intro x,
ext m,
have h₀ : -x.to_aff_vec_coord_tuple.vec m + x.to_aff_vec_coord_tuple.vec m = 0 := add_left_neg (x.1.1 m),
have h₁ : (0 : aff_coord_vec K n fr).to_aff_vec_coord_tuple.vec m = (0 : K) := rfl,
have h₂ : (-x + x).to_aff_vec_coord_tuple.vec m = -x.to_aff_vec_coord_tuple.vec m + x.to_aff_vec_coord_tuple.vec m := begin
    have h₃ : (-x + x).1.1 m = (-x).1.1 m + x.1.1 m := rfl,
    have h₄ : -x = vec_neg_coord K n fr ⟨x.1⟩ := begin
        have h : x = ⟨x.1⟩ := by {ext, refl},
        rw h,
        refl
    end,
    have h₅ : vec_neg_coord K n fr ⟨x.1⟩ = ⟨⟨λ m : fin n, -(x.1.1 m)⟩⟩ := rfl,
    rw [h₃, h₄, h₅]
end,
exact eq.trans h₂ (eq.trans h₀ (eq.symm h₁)),
end


lemma vec_add_comm_coord : ∀ x y : aff_coord_vec K n fr, x + y = y + x :=
begin
intros x y,
ext m,
exact add_comm (x.1.1 m) (y.1.1 m),
end

/-! ### Type class instance for abelian group -/
instance aff_comm_group_coord : add_comm_group (aff_coord_vec K n fr) :=
begin
split,
exact vec_add_left_neg_coord K n fr,
exact vec_add_comm_coord K n fr,
exact vec_add_assoc_coord K n fr,
exact vec_zero_add_coord K n fr,
exact vec_add_zero_coord K n fr,
end



/-! ### Scalar action -/

@[ext]
def vec_scalar_coord : K → aff_coord_vec K n fr → aff_coord_vec K n fr :=
    λ a x, ⟨vec_scalar K n a x.1⟩

instance : has_scalar K (aff_coord_vec K n fr) := ⟨vec_scalar_coord K n fr⟩

lemma vec_one_smul_coord : (1 : K) • cv1 = cv1 := 
begin
dsimp only [has_scalar.smul, vec_scalar_coord],
have h₀ : vec_scalar K n 1 cv1.to_aff_vec_coord_tuple = cv1.1 := vec_one_smul K n cv1.1,
rw h₀,
ext m,
refl,
end

lemma vec_mul_smul_coord : ∀ g h : K, ∀ x : aff_coord_vec K n fr, (g * h) • x = g • h • x :=
begin
intros,
have h₀ := vec_mul_smul K n g h x.1,
dsimp only [has_scalar.smul, vec_scalar_coord] at h₀ ⊢,
rw h₀,
end

instance : mul_action K (aff_coord_vec K n fr) := ⟨vec_one_smul_coord K n fr, vec_mul_smul_coord K n fr⟩

lemma vec_smul_add_coord : ∀ g : K, ∀ x y : aff_coord_vec K n fr, g • (x + y) = g•x + g•y :=
begin
intros,
have h₀ := vec_smul_add K n g x.1 y.1,
dsimp only [has_scalar.smul, vec_scalar_coord, has_add.add, vec_add_coord] at h₀ ⊢,
rw h₀,
end

lemma vec_smul_zero_coord : ∀ g : K, g • (0 : aff_coord_vec K n fr) = 0 :=
begin
intros,
have h₀ := vec_smul_zero K n g,
dsimp only [has_scalar.smul, vec_scalar_coord, has_zero.zero, vec_zero_coord] at h₀ ⊢,
rw h₀,
end

instance : distrib_mul_action K (aff_coord_vec K n fr) := ⟨vec_smul_add_coord K n fr, vec_smul_zero_coord K n fr⟩

lemma vec_add_smul_coord : ∀ g h : K, ∀ x : aff_coord_vec K n fr, (g + h) • x = g•x + h•x :=
begin
intros,
have h₀ := vec_add_smul K n g h x.1,
dsimp only [has_scalar.smul, vec_scalar_coord, has_add.add, vec_add_coord] at h₀ ⊢,
rw h₀,
end

lemma vec_zero_smul_coord : ∀ x : aff_coord_vec K n fr, (0 : K) • x = 0 :=
begin
intros,
have h₀ := vec_zero_smul K n x.1,
dsimp only [has_scalar.smul, vec_scalar_coord, has_zero.zero, vec_zero_coord] at h₀ ⊢,
rw h₀,
end

instance aff_semimod_coord : semimodule K (aff_coord_vec K n fr) := ⟨vec_add_smul_coord K n fr, vec_zero_smul_coord K n fr⟩

instance aff_module_coord : module K (aff_coord_vec K n fr) := ⟨vec_add_smul_coord K n fr, vec_zero_smul_coord K n fr⟩

/-! ### group action of aff_vec_coord_tuple on aff_pt_coord_tuple -/

def aff_group_action_coord : aff_coord_vec K n fr → aff_coord_pt K n fr → aff_coord_pt K n fr :=
    λ x y, ⟨aff_group_action K n x.1 y.1⟩


def aff_group_sub_coord : aff_coord_pt K n fr → aff_coord_pt K n fr → aff_coord_vec K n fr :=
    λ x y, ⟨aff_group_sub K n x.1 y.1⟩

#check add_action

instance : has_vadd (aff_coord_vec K n fr) (aff_coord_pt K n fr) := ⟨aff_group_action_coord K n fr⟩

instance : has_vsub (aff_coord_vec K n fr) (aff_coord_pt K n fr) := ⟨aff_group_sub_coord K n fr⟩

lemma aff_zero_sadd_coord : ∀ x : aff_coord_pt K n fr, (0 : aff_coord_vec K n fr) +ᵥ x = x :=
begin
intros,
have h₀ := aff_zero_sadd K n x.1,
dsimp only [has_vadd.vadd, aff_group_action_coord, has_zero.zero, vec_zero_coord] at h₀ ⊢,
rw h₀,
ext m,
refl,
end

lemma aff_add_sadd_coord : ∀ x y : aff_coord_vec K n fr, ∀ a : aff_coord_pt K n fr, x +ᵥ (y +ᵥ a) = x + y +ᵥ a :=
begin
intros,
have h₀ := aff_add_sadd K n x.1 y.1 a.1,
dsimp only [has_add.add, vec_add_coord, has_vadd.vadd, aff_group_action_coord] at h₀ ⊢,
rw h₀,
end

instance : add_action (aff_coord_vec K n fr) (aff_coord_pt K n fr) := ⟨aff_group_action_coord K n fr, aff_zero_sadd_coord K n fr, aff_add_sadd_coord K n fr⟩

lemma aff_add_trans_coord : ∀ a b : aff_coord_pt K n fr, ∃ x : aff_coord_vec K n fr, x +ᵥ a = b :=
begin
intros,
apply exists.intro (b -ᵥ a),
have h₀ := aff_vsub_vadd K n b.1 a.1,
dsimp only [has_vadd.vadd, aff_group_action_coord, has_vsub.vsub, aff_group_sub_coord] at h₀ ⊢,
rw h₀,
ext m,
refl,
end

lemma aff_add_free_coord : ∀ a : aff_coord_pt K n fr, ∀ g h : aff_coord_vec K n fr, g +ᵥ a = h +ᵥ a → g = h :=
begin
intros a g h h₀,
have h₁ := aff_add_free K n a.1 g.1 h.1,
dsimp only [has_vadd.vadd, aff_group_action_coord] at h₀ h₁,
have h₂ : ∀ (x y : aff_coord_pt K n fr), x = y → x.to_aff_pt_coord_tuple = y.to_aff_pt_coord_tuple := begin
    intros x y hy,
    rw hy
end,
have h₃ : aff_coord_pt.mk (aff_group_action K n g.to_aff_vec_coord_tuple a.to_aff_pt_coord_tuple) = 
    aff_coord_pt.mk (aff_group_action K n h.to_aff_vec_coord_tuple a.to_aff_pt_coord_tuple) →
    (aff_coord_pt.mk (aff_group_action K n g.to_aff_vec_coord_tuple a.to_aff_pt_coord_tuple)).to_aff_pt_coord_tuple =
    (aff_coord_pt.mk (aff_group_action K n h.to_aff_vec_coord_tuple a.to_aff_pt_coord_tuple)).to_aff_pt_coord_tuple := by apply h₂,
have h₄ := h₃ h₀,
have h₅ : (aff_coord_pt.mk (aff_group_action K n g.to_aff_vec_coord_tuple a.to_aff_pt_coord_tuple)).to_aff_pt_coord_tuple =
    aff_group_action K n g.to_aff_vec_coord_tuple a.to_aff_pt_coord_tuple := rfl,
have h₆ : (aff_coord_pt.mk (aff_group_action K n h.to_aff_vec_coord_tuple a.to_aff_pt_coord_tuple)).to_aff_pt_coord_tuple =
    aff_group_action K n h.to_aff_vec_coord_tuple a.to_aff_pt_coord_tuple := rfl,
rw [h₅, h₆] at h₄,
have h₇ := h₁ h₄,
ext,
rw h₇
end

lemma aff_vadd_vsub_coord : ∀ (x : aff_coord_vec K n fr) (a : aff_coord_pt K n fr), x +ᵥ a -ᵥ a = x := 
begin
intros,
have h₀ := aff_vadd_vsub K n x.1 a.1,
dsimp only [has_vadd.vadd, aff_group_action_coord, has_vsub.vsub, aff_group_sub_coord] at h₀ ⊢,
rw h₀,
ext m,
refl,
end

lemma aff_vsub_vadd_coord : ∀ a b : aff_coord_pt K n fr, (a -ᵥ b) +ᵥ b = a :=
begin
intros,
have h₀ := aff_vsub_vadd K n a.1 b.1,
dsimp only [has_vadd.vadd, aff_group_action_coord, has_vsub.vsub, aff_group_sub_coord] at h₀ ⊢,
rw h₀,
ext m,
refl,
end

instance : nonempty (aff_coord_pt K n fr) := ⟨⟨pt_zero K n⟩⟩

instance aff_torsor_coord : add_torsor (aff_coord_vec K n fr) (aff_coord_pt K n fr) := 
⟨aff_group_action_coord K n fr, 
aff_zero_sadd_coord K n fr,
aff_add_sadd_coord K n fr,
aff_group_sub_coord K n fr,
aff_vsub_vadd_coord K n fr, 
aff_vadd_vsub_coord K n fr⟩

/-
"THEOREM:" these sets of scalar tuples with the operations defined on them
do have the structure of an affine space.
-/

instance aff_coord_is : 
    affine_space 
        (aff_coord_vec K n fr) 
        (aff_coord_pt K n fr) := 
    ⟨aff_group_action_coord K n fr, 
aff_zero_sadd_coord K n fr,
aff_add_sadd_coord K n fr,
aff_group_sub_coord K n fr,
aff_vsub_vadd_coord K n fr, 
aff_vadd_vsub_coord K n fr⟩

def pt_plus_vec
    {X : Type u} 
    {K : Type v} 
    {V : Type w} 
    {n : ℕ}
    {ι : Type*}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {fr : affine_coord_frame K n} :
    (aff_coord_pt K n fr) → 
    (aff_coord_vec K n fr) → 
    (aff_coord_pt K n fr) 
| p v := aff_group_action_coord K n fr v p

notation
 pt +ᵥ v := pt_plus_vec pt v

 
def vec_mul_scalar
    {X : Type u} 
    {K : Type v} 
    {V : Type w} 
    {n : ℕ}
    {ι : Type*}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {fr : affine_coord_frame K n} :
    (aff_coord_vec K n fr) → 
    K → 
    (aff_coord_vec K n fr) 
| v s := s • v

notation
 v • s := vec_mul_scalar v s
 
def pt_minus_vec
    {X : Type u} 
    {K : Type v} 
    {V : Type w} 
    {n : ℕ}
    {ι : Type*}
    [inhabited K] 
    [field K] 
    [add_comm_group V] 
    [module K V] 
    [vector_space K V] 
    [affine_space V X]
    {fr : affine_coord_frame K n} :
    (aff_coord_pt K n fr) → 
    (aff_coord_vec K n fr) → 
    (aff_coord_pt K n fr) 
| p v := aff_group_action_coord K n fr (vec_neg_coord K n fr v) p

notation
 pt -ᵥ v := pt_minus_vec pt v

end aff_fr