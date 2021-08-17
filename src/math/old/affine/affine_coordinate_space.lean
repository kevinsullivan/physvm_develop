import linear_algebra.affine_space.basic
import linear_algebra.basis

open_locale affine

universes u v w x

variables 
    (K : Type v) 
    (n : ℕ) 
    [inhabited K] 
    [field K]

open list
--open vecl



@[ext]
structure aff_vec_coord_tuple :=
(vec : fin n → K)

/-- type of affine points represented by coordinate tuples -/
@[ext]
structure aff_pt_coord_tuple :=
(pt : fin n → K)


instance vec_coe : has_coe (aff_vec_coord_tuple K n) (fin n → K) := ⟨λv,v.1⟩
instance pt_coe : has_coe (aff_pt_coord_tuple K n) (fin n → K) := ⟨λp,p.1⟩


variables (x y : aff_vec_coord_tuple K n) (a b : aff_pt_coord_tuple K n)
    

def fin_add : (fin n → K) → (fin n → K) → (fin n → K) := λ x y, (λ m : fin n, x m + y m)

/-! ### abelian group operations -/
def vec_add : aff_vec_coord_tuple K n → aff_vec_coord_tuple K n → aff_vec_coord_tuple K n :=
    λ x y, ⟨λ m : fin n, x.1 m + y.1 m⟩
def vec_zero : aff_vec_coord_tuple K n := ⟨λ m : fin n, 0⟩
def vec_neg : aff_vec_coord_tuple K n → aff_vec_coord_tuple K n
| x := ⟨λ m : fin n, -(x.1 m)⟩

/-! ### type class instances for the abelian group operations -/
instance : has_add (aff_vec_coord_tuple K n) := ⟨vec_add K n⟩
instance : has_zero (aff_vec_coord_tuple K n) := ⟨vec_zero K n⟩
instance : has_neg (aff_vec_coord_tuple K n) := ⟨vec_neg K n⟩

-- misc
def pt_zero : aff_pt_coord_tuple K n := ⟨λ m : fin n, 0⟩

lemma vec_zero_id : (0 : aff_vec_coord_tuple K n) = vec_zero K n := rfl

lemma vec_zero_is_zero (m : fin n) : (vec_zero K n).vec m = 0 := rfl

-- properties necessary to show aff_vec_coord_tuple K n is an instance of add_comm_group
#print add_comm_group
lemma vec_add_assoc : ∀ x y z : aff_vec_coord_tuple K n, x + y + z = x + (y + z) :=
begin
intros,
cases x,
cases y,
cases z,
ext m,
exact add_assoc (x m) (y m) (z m),
end

lemma vec_zero_add : ∀ x : aff_vec_coord_tuple K n, 0 + x = x :=
begin
intro x,
cases x,
ext m,
exact zero_add (x m),
end

lemma vec_add_zero : ∀ x : aff_vec_coord_tuple K n, x + 0 = x :=
begin
intro x,
cases x,
ext m,
exact add_zero (x m),
end

lemma vec_add_left_neg : ∀ x : aff_vec_coord_tuple K n, -x + x = 0 :=
begin
intro x,
cases x,
ext m,
exact add_left_neg (x m),
end

lemma vec_add_comm : ∀ x y : aff_vec_coord_tuple K n, x + y = y + x :=
begin
intros x y,
cases x,
cases y,
ext m,
exact add_comm (x m) (y m),
end

/-! ### Type class instance for abelian group -/
instance aff_comm_group : add_comm_group (aff_vec_coord_tuple K n) :=
begin
split,
exact vec_add_left_neg K n,
exact vec_add_comm K n,
exact vec_add_assoc K n,
exact vec_zero_add K n,
exact vec_add_zero K n,
end



/-! ### Scalar action -/


@[ext]
def vec_scalar : K → aff_vec_coord_tuple K n → aff_vec_coord_tuple K n :=
    λ a x, ⟨λ m : fin n, a * x.1 m⟩

instance : has_scalar K (aff_vec_coord_tuple K n) := ⟨vec_scalar K n⟩

lemma vec_one_smul : (1 : K) • x = x := 
begin
cases x,
ext m,
exact one_mul (x m),
end

lemma vec_mul_smul : ∀ g h : K, ∀ x : aff_vec_coord_tuple K n, (g * h) • x = g • h • x :=
begin
intros,
cases x,
ext m,
exact mul_assoc g h (x m),
end

instance : mul_action K (aff_vec_coord_tuple K n) := ⟨vec_one_smul K n, vec_mul_smul K n⟩

lemma vec_smul_add : ∀ g : K, ∀ x y : aff_vec_coord_tuple K n, g • (x + y) = g•x + g•y :=
begin
intros,
cases x,
cases y,
ext m,
exact left_distrib g (x m) (y m),
end

lemma vec_smul_zero : ∀ g : K, g • (0 : aff_vec_coord_tuple K n) = 0 :=
begin
intros,
dsimp [vec_zero_id, vec_zero, has_scalar.smul, vec_scalar],
rw mul_zero g,
end

instance : distrib_mul_action K (aff_vec_coord_tuple K n) := ⟨vec_smul_add K n, vec_smul_zero K n⟩

lemma vec_add_smul : ∀ g h : K, ∀ x : aff_vec_coord_tuple K n, (g + h) • x = g•x + h•x :=
begin
intros,
cases x,
ext m,
exact right_distrib g h (x m),
end

lemma vec_zero_smul : ∀ x : aff_vec_coord_tuple K n, (0 : K) • x = 0 :=
begin
intros,
cases x,
ext m,
exact zero_mul (x m),
end

instance aff_semimod : semimodule K (aff_vec_coord_tuple K n) := ⟨vec_add_smul K n, vec_zero_smul K n⟩

instance aff_module : module K (aff_vec_coord_tuple K n) := aff_semimod K n

/-! ### group action of aff_vec_coord_tuple on aff_pt_coord_tuple -/


def aff_group_action : aff_vec_coord_tuple K n → aff_pt_coord_tuple K n → aff_pt_coord_tuple K n :=
    λ x y, ⟨λ m : fin n, x.1 m + y.1 m⟩


def aff_group_sub : aff_pt_coord_tuple K n → aff_pt_coord_tuple K n → aff_vec_coord_tuple K n :=
    λ x y, ⟨λ m : fin n, x.1 m - y.1 m⟩

#check add_action

instance : has_vadd (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n) := ⟨aff_group_action K n⟩

instance : has_vsub (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n) := ⟨aff_group_sub K n⟩

lemma aff_zero_sadd : ∀ x : aff_pt_coord_tuple K n, (0 : aff_vec_coord_tuple K n) +ᵥ x = x :=
begin
intro x,
cases x,
ext m,
exact zero_add (x m),
end

lemma aff_add_sadd : ∀ x y : aff_vec_coord_tuple K n, ∀ a : aff_pt_coord_tuple K n, x +ᵥ (y +ᵥ a) = x + y +ᵥ a :=
begin
intros,
cases x,
cases y,
cases a,
ext m,
exact eq.symm (add_assoc (x m) (y m) (a m)),
end

lemma aff_vadd_vsub : ∀ (x : aff_vec_coord_tuple K n) (a : aff_pt_coord_tuple K n), x +ᵥ a -ᵥ a = x := 
begin
intros,
ext m,
exact add_sub_cancel (x.vec m) (a.pt m),
end

instance : add_action (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n) := ⟨aff_group_action K n, aff_zero_sadd K n, aff_add_sadd K n⟩

lemma aff_vsub_vadd : ∀ a b : aff_pt_coord_tuple K n, (a -ᵥ b) +ᵥ b = a :=
begin
intros,
ext m, 
exact sub_add_cancel (a.pt m) (b.pt m),
end

lemma aff_add_trans : ∀ a b : aff_pt_coord_tuple K n, ∃ x : aff_vec_coord_tuple K n, x +ᵥ a = b :=
by {intros, apply exists.intro (b -ᵥ a), exact aff_vsub_vadd K n b a}

lemma aff_add_free : ∀ a : aff_pt_coord_tuple K n, ∀ g h : aff_vec_coord_tuple K n, g +ᵥ a = h +ᵥ a → g = h :=
begin
intros a g h h₀,
have h₁ : g +ᵥ a -ᵥ a = h +ᵥ a -ᵥ a := by rw h₀,
rw [aff_vadd_vsub K n g a, aff_vadd_vsub K n h a] at h₁,
exact h₁,
end

instance : nonempty (aff_pt_coord_tuple K n) := ⟨pt_zero K n⟩

instance aff_torsor : add_torsor (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n) := 
⟨aff_group_action K n, 
aff_zero_sadd K n,
aff_add_sadd K n,
aff_group_sub K n,
aff_vsub_vadd K n, 
aff_vadd_vsub K n⟩


instance aff_coord_is : 
    affine_space 
        (aff_vec_coord_tuple K n) 
        (aff_pt_coord_tuple K n) := 
    aff_torsor K n


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
    [affine_space V X] :
    (aff_pt_coord_tuple K n) → 
    (aff_vec_coord_tuple K n) → 
    (aff_pt_coord_tuple K n) 
| p v := aff_group_action K n v p

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
    [affine_space V X] :
    (aff_vec_coord_tuple K n) → 
    K → 
    (aff_vec_coord_tuple K n) 
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
    [affine_space V X]:
    (aff_pt_coord_tuple K n) → 
    (aff_vec_coord_tuple K n) → 
    (aff_pt_coord_tuple K n) 
| p v := aff_group_action K n (-v) p

notation
 pt -ᵥ v := pt_minus_vec pt v
/-
NEW FILE
-/