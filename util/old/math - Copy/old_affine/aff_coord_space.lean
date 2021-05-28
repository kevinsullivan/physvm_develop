import .affine
import .list_stuff
import .add_group_action linear_algebra.basis
import algebra.field tactic.ext

universes u v w
variables (X : Type u) (K : Type v) (V : Type w) (n : ℕ) (id : ℕ) (k : K)
[inhabited K] [field K] [add_comm_group V] [vector_space K V] [affine_space X K V]

open list
/-- type class for affine vectors. This models n-dimensional K-coordinate space. -/
@[ext]
structure aff_vec_coord_tuple :=
(l : list K)
(len_fixed : l.length = n + 1)
(fst_zero : head l = 0)

/-- type class for affine points for coordinate spaces. -/
@[ext]
structure aff_pt_coord_tuple :=
(l : list K)
(len_fixed : l.length = n + 1)
(fst_one : head l = 1)

-- coordinate tuple
-- aff_pt_coord_tuple, aff_vec_coord_tuple

/-
structure aff_vec_coord_tuple :=    -- an affine vector tuple + a frame
(c : aff_vec_coord_tuple_coord_tuple K n)
(f : frame) -- this can be either std_frame or new_frame relative to some old_frame

/-- type class for affine points for coordinate spaces. -/
structure aff_pt_coord_tuple :=     -- an affine point tuple with a frame
(l : list K)
(len_fixed : l.length = n + 1)
(fst_one : head l = 1)
-/


variables (x y : aff_vec_coord_tuple K n) (a b : aff_pt_coord_tuple K n)

-- lemmas so that the following operations are well-defined
/-- the length of the sum of two length n+1 vectors is n+1 -/
lemma list_sum_fixed : length (x.1 + y.1) = n + 1 := 
    by simp only [sum_test K x.1 y.1, length_sum x.1 y.1, x.2, y.2, min_self]

lemma aff_not_nil : x.1 ≠ [] := 
begin
intro h,
have f : 0 ≠ n + 1 := ne.symm (nat.succ_ne_zero n),
have len_x_nil : length x.1 = length nil := by rw h,
have len_fixed : length nil = n + 1 := eq.trans (eq.symm len_x_nil) x.2,
have bad : 0 = n + 1 := eq.trans (eq.symm len_nil) len_fixed,
contradiction,
end

lemma aff_cons : ∃ x_hd : K, ∃ x_tl : list K, x.1 = x_hd :: x_tl :=
begin
cases x,
cases x_l,
{
    have f : 0 ≠ n + 1 := ne.symm (nat.succ_ne_zero n),
    have bad := eq.trans (eq.symm len_nil) x_len_fixed,
    contradiction
},
{
    apply exists.intro x_l_hd,
    apply exists.intro x_l_tl,
    exact rfl
}
end

/-- head is compatible with addition -/
lemma head_sum : head x.1 + head y.1 = head (x.1 + y.1) := 
begin
cases x,
cases y,
cases x_l,
    have f : 0 ≠ n + 1 := ne.symm (nat.succ_ne_zero n),
    have bad := eq.trans (eq.symm len_nil) x_len_fixed,
    contradiction,
cases y_l,
    have f : 0 ≠ n + 1 := ne.symm (nat.succ_ne_zero n),
    have bad := eq.trans (eq.symm len_nil) y_len_fixed,
    contradiction,
have head_xh : head (x_l_hd :: x_l_tl) = x_l_hd := rfl,
have head_yh : head (y_l_hd :: y_l_tl) = y_l_hd := rfl,
rw head_xh at x_fst_zero,
rw head_yh at y_fst_zero,
simp [x_fst_zero, y_fst_zero, sum_test, add_cons_cons 0 0 x_l_tl y_l_tl],
end

/-- the head of the sum of two vectors is 0 -/
lemma sum_fst_fixed : head (x.1 + y.1) = 0 :=
    by simp only [eq.symm (head_sum K n x y), x.3, y.3]; exact add_zero 0

/-- the length of the zero vector is n+1 -/
lemma len_zero : length (field_zero K n) = n + 1 :=
begin
induction n with n',
refl,
{
have h₃ : nat.succ (n' + 1) = nat.succ n' + 1 := rfl,
have h₄ : length (field_zero K (nat.succ n')) = nat.succ (n' + 1) :=
    by {rw eq.symm n_ih, refl},
rw eq.symm h₃,
exact h₄,
}
end

/-- the head of the zero vector is zero -/
lemma head_zero : head (field_zero K n) = 0 := by {cases n, refl, refl}


lemma vec_len_neg : length (neg K x.1) = n + 1 := by {simp only [len_neg], exact x.2}


lemma head_neg_0 : head (neg K x.1) = 0 :=
begin
cases x,
cases x_l,
contradiction,
rw neg_cons K x_l_hd x_l_tl,
have head_xh : head (x_l_hd :: x_l_tl) = x_l_hd := rfl,
have head_0 : head (0 :: neg K x_l_tl) = 0 := rfl,
rw head_xh at x_fst_zero,
simp only [x_fst_zero, neg_zero, head_0],
end


/-! ### abelian group operations -/
def vec_add : aff_vec_coord_tuple K n → aff_vec_coord_tuple K n → aff_vec_coord_tuple K n :=
    λ x y, ⟨x.1 + y.1, list_sum_fixed K n x y, sum_fst_fixed K n x y⟩
def vec_zero : aff_vec_coord_tuple K n := ⟨field_zero K n, len_zero K n, head_zero K n⟩
def vec_neg : aff_vec_coord_tuple K n → aff_vec_coord_tuple K n
| ⟨l, len, fst⟩ := ⟨list.neg K l, vec_len_neg K n ⟨l, len, fst⟩, head_neg_0 K n ⟨l, len, fst⟩⟩


/-! ### type class instances for the abelian group operations -/
instance : has_add (aff_vec_coord_tuple K n) := ⟨vec_add K n⟩
instance : has_zero (aff_vec_coord_tuple K n) := ⟨vec_zero K n⟩
instance : has_neg (aff_vec_coord_tuple K n) := ⟨vec_neg K n⟩

-- misc
def pt_zero_f : ℕ → list K 
| 0 := [1]
| (nat.succ n) := [1] ++ list.field_zero K n

#check list.append

lemma pt_zero_len : length (pt_zero_f K n) = n + 1 :=
begin
induction n with n',
{refl},
{
    cases n' with n'',
    {refl},
    {
        have h₁ : pt_zero_f K n''.succ = [1] ++ field_zero K n'' := rfl,
        have h₂ : ([1] ++ field_zero K n'').length = (field_zero K n'').length + 1 := rfl,
        rw [h₁, h₂] at n_ih,

        have h₃ : pt_zero_f K n''.succ.succ = [1] ++ field_zero K n''.succ := rfl,
        have h₄ : ([1] ++ field_zero K n''.succ).length = (field_zero K n''.succ).length + 1 := rfl,
        have h₅ : field_zero K n''.succ = 0 :: (field_zero K n'') := rfl,
        have h₆ : (0 :: field_zero K n'').length = (field_zero K n'').length + 1 := rfl,
        rw [h₃, h₄, h₅, h₆, n_ih]
    }
}
end

lemma pt_zero_hd : head (pt_zero_f K n) = 1 := by {cases n, refl, refl} 

def pt_zero : aff_pt_coord_tuple K n := ⟨pt_zero_f K n, pt_zero_len K n, pt_zero_hd K n⟩

lemma vec_zero_is : (0 : aff_vec_coord_tuple K n) = vec_zero K n := rfl

lemma vec_zero_list' : (0 : aff_vec_coord_tuple K n).1 = field_zero K n := rfl

-- properties necessary to show aff_vec_coord_tuple K n is an instance of add_comm_group
#print add_comm_group
lemma vec_add_assoc : ∀ x y z : aff_vec_coord_tuple K n, x + y + z = x + (y + z) :=
begin
intros,
cases x,
cases y,
cases z,
ext;
split,
{
    intro h,
    dsimp [has_add.add, vec_add] at h,
    dsimp [has_add.add, vec_add],
    rw [list.ladd_is, list.ladd_is] at h,
    rw [list.ladd_is, list.ladd_is],
    rw list.add_assoc at h,
    exact h
},
{
    intro h,
    dsimp [has_add.add, vec_add] at h,
    dsimp [has_add.add, vec_add],
    rw [list.ladd_is, list.ladd_is] at h,
    rw [list.ladd_is, list.ladd_is],
    rw list.add_assoc,
    exact h
}
end

lemma vec_zero_add : ∀ x : aff_vec_coord_tuple K n, 0 + x = x :=
begin
intro x,
cases x,
rw vec_zero_is,
ext,
split,
intros,
dsimp [has_add.add, vec_add, vec_zero] at a_1,
change a ∈ ((field_zero K n) + x_l).nth n_1 at a_1,
rw list.zero_add' K x_l n x_len_fixed at a_1,
exact a_1,

intros,
dsimp [has_add.add, vec_add, vec_zero],
change a ∈ ((field_zero K n) + x_l).nth n_1,
rw list.zero_add' K x_l n x_len_fixed,
exact a_1,
end


lemma vec_add_zero : ∀ x : aff_vec_coord_tuple K n, x + 0 = x :=
begin
intro x,
cases x,
rw vec_zero_is,
ext,
split,
intros,
dsimp [has_add.add, vec_add, vec_zero] at a_1,
change a ∈ (x_l + (field_zero K n)).nth n_1 at a_1,
rw list.add_zero' K x_l n x_len_fixed at a_1,
exact a_1,

intros,
dsimp [has_add.add, vec_add, vec_zero],
change a ∈ (x_l + (field_zero K n)).nth n_1,
rw list.add_zero' K x_l n x_len_fixed,
exact a_1,
end

lemma vec_add_left_neg : ∀ x : aff_vec_coord_tuple K n, -x + x = 0 :=
begin
intro x,
cases x,
have h₁ : (0 : aff_vec_coord_tuple K n) = ⟨field_zero K n, len_zero K n, head_zero K n⟩ := rfl,
rw h₁,
ext;
split,
{
    intro h,
    dsimp [has_neg.neg, vec_neg, has_add.add, vec_add] at h,
    dsimp [has_neg.neg, vec_neg, has_add.add, vec_add],
    rw [list.ladd_is, list.add_left_neg] at h,
    {
        have h₃ : x_l.length - 1 = n := by {rw x_len_fixed, refl},
        rw h₃ at h,
        exact h
    },
    {
        cases x_l,
        contradiction,
        contradiction
    }
},
{
    intro h,
    dsimp [has_neg.neg, vec_neg, has_add.add, vec_add] at h,
    dsimp [has_neg.neg, vec_neg, has_add.add, vec_add],
    have h₂ : ladd (neg K x_l) x_l = neg K x_l + x_l := rfl,
    rw h₂,
    rw list.add_left_neg,
    {
        have h₃ : x_l.length - 1 = n := by {rw x_len_fixed, refl},
        rw h₃,
        exact h
    },
    {
        cases x_l,
        contradiction,
        contradiction
    }
}
end

#check ladd

lemma vec_add_comm : ∀ x y : aff_vec_coord_tuple K n, x + y = y + x :=
begin
intros x y,
cases x,
cases y,
ext,
split,
intros,
dsimp [has_add.add, vec_add],
dsimp [has_add.add, vec_add] at a_1,
change a ∈ (y_l + x_l).nth n_1,
rw list.add_comm,
exact a_1,

intros,
dsimp [has_add.add, vec_add],
dsimp [has_add.add, vec_add] at a_1,
change a ∈ (x_l + y_l).nth n_1,
rw list.add_comm,
exact a_1,
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
#check semimodule
#check distrib_mul_action
lemma scale_head : head (field_scalar K k x.1) = 0 :=
begin
cases x,
cases x_l,
rw scalar_nil,
contradiction,
have hd0 : x_l_hd = 0 := x_fst_zero,
rw [scalar_cons, hd0, mul_zero],
refl,
end

@[ext]
def vec_scalar : K → aff_vec_coord_tuple K n → aff_vec_coord_tuple K n :=
    λ a x, ⟨field_scalar K a x.1, trans (scale_len K a x.1) x.2, scale_head K n a x⟩

instance : has_scalar K (aff_vec_coord_tuple K n) := ⟨vec_scalar K n⟩

lemma vec_one_smul : (1 : K) • x = x := 
begin
cases x,
ext,
split,
intros,
dsimp only [has_scalar.smul, vec_scalar] at a_1,
rw list.one_smul_cons at a_1,
exact a_1,

intros,
dsimp only [has_scalar.smul, vec_scalar],
rw list.one_smul_cons,
exact a_1,
end

lemma vec_mul_smul : ∀ g h : K, ∀ x : aff_vec_coord_tuple K n, (g * h) • x = g • h • x :=
begin
intros,
cases x,
ext;
split,
{
    intro hy,
    dsimp only [has_scalar.smul, vec_scalar] at hy,
    dsimp only [has_scalar.smul, vec_scalar],
    rw list.smul_assoc at hy,
    exact hy
},
{
    intro hy,
    dsimp only [has_scalar.smul, vec_scalar] at hy,
    dsimp only [has_scalar.smul, vec_scalar],
    rw list.smul_assoc,
    exact hy
}
end

instance : mul_action K (aff_vec_coord_tuple K n) := ⟨vec_one_smul K n, vec_mul_smul K n⟩

lemma vec_smul_add : ∀ g : K, ∀ x y : aff_vec_coord_tuple K n, g • (x + y) = g•x + g•y :=
begin
intros,
cases x,
cases y,
ext;
split,
{
    intro h,
    dsimp only [has_add.add, vec_add, has_scalar.smul, vec_scalar] at h,
    dsimp only [has_add.add, vec_add, has_scalar.smul, vec_scalar],
    rw list.ladd_is at h,
    rw list.ladd_is,
    rw list.smul_add at h,
    exact h
},
{
    
    intro h,
    dsimp only [has_add.add, vec_add, has_scalar.smul, vec_scalar] at h,
    dsimp only [has_add.add, vec_add, has_scalar.smul, vec_scalar],
    rw list.ladd_is at h,
    rw list.ladd_is,
    rw list.smul_add,
    exact h
}
end

lemma vec_smul_zero : ∀ g : K, g • (0 : aff_vec_coord_tuple K n) = 0 :=
begin
intro,
have h₁ : (0 : aff_vec_coord_tuple K n) = ⟨field_zero K n, len_zero K n, head_zero K n⟩ := rfl,
rw h₁,
cases (vec_zero K n),
ext;
split,
{
    intro h,
    dsimp only [has_scalar.smul, vec_scalar] at h,
    dsimp only [has_scalar.smul, vec_scalar],
    rw list.smul_zero at h,
    exact h
},
{
    intro h,
    dsimp only [has_scalar.smul, vec_scalar] at h,
    dsimp only [has_scalar.smul, vec_scalar],
    rw list.smul_zero,
    exact h
}
end

instance : distrib_mul_action K (aff_vec_coord_tuple K n) := ⟨vec_smul_add K n, vec_smul_zero K n⟩

lemma vec_add_smul : ∀ g h : K, ∀ x : aff_vec_coord_tuple K n, (g + h) • x = g•x + h•x :=
begin
intros,
cases x,
ext;
split,
{
    intro hy,
    dsimp only [has_add.add, vec_add, has_scalar.smul, vec_scalar] at hy,
    dsimp only [has_add.add, vec_add, has_scalar.smul, vec_scalar],
    have h₁ : distrib.add g h = g + h := rfl,
    rw h₁ at hy,
    rw list.ladd_is,
    rw list.add_smul at hy,
    exact hy
},
{
    intro hy,
    dsimp only [has_add.add, vec_add, has_scalar.smul, vec_scalar] at hy,
    dsimp only [has_add.add, vec_add, has_scalar.smul, vec_scalar],
    have h₁ : distrib.add g h = g + h := rfl,
    rw list.ladd_is at hy,
    rw h₁,
    rw list.add_smul,
    exact hy
}
end

lemma vec_zero_smul : ∀ x : aff_vec_coord_tuple K n, (0 : K) • x = 0 :=
begin
intro,
have h₁ : (0 : aff_vec_coord_tuple K n) = ⟨field_zero K n, len_zero K n, head_zero K n⟩ := rfl,
rw h₁,
cases (vec_zero K n),
cases x,
ext;
split,
{
    have x_not_nil : x_l ≠ nil := by {cases x_l, contradiction, contradiction},
    intro h,
    dsimp only [has_scalar.smul, vec_scalar] at h,
    dsimp only [has_scalar.smul, vec_scalar],
    rw list.zero_smul at h,
    {
        have h₂ : x_l.length - 1 = n := by {rw x_len_fixed, refl},
        rw h₂ at h,
        exact h
    },
    exact x_not_nil,
},
{
    have x_not_nil : x_l ≠ nil := by {cases x_l, contradiction, contradiction},
    intro h,
    dsimp only [has_scalar.smul, vec_scalar] at h,
    dsimp only [has_scalar.smul, vec_scalar],
    rw list.zero_smul,
    {
        have h₂ : x_l.length - 1 = n := by {rw x_len_fixed, refl},
        rw h₂,
        exact h
    },
    exact x_not_nil,
}
end

instance aff_semimod : semimodule K (aff_vec_coord_tuple K n) := ⟨vec_add_smul K n, vec_zero_smul K n⟩

instance aff_module : module K (aff_vec_coord_tuple K n) := aff_semimod K n

-- need to define scalar multiplication to show it's a module
instance aff_vec_coord_tuple_space : vector_space K (aff_vec_coord_tuple K n) := aff_module K n

/-! ### group action of aff_vec_coord_tuple on aff_pt_coord_tuple -/
-- Proof that for any vector x and point y, x.length + y.length = (x ⊹ y).length
lemma list_action_fixed : ∀ x : aff_vec_coord_tuple K n, ∀ y : aff_pt_coord_tuple K n, length (x.1 + y.1) = n + 1 := 
    by {intros, simp only [sum_test K x.1 y.1, length_sum x.1 y.1, x.2, y.2, min_self]}

/-- head is compatible with addition -/
lemma head_action : ∀ x : aff_vec_coord_tuple K n, ∀ y : aff_pt_coord_tuple K n, head x.1 + head y.1 = head (x.1 + y.1) := 
begin
intros,
cases x,
cases y,
cases x_l,
    have f : 0 ≠ n + 1 := ne.symm (nat.succ_ne_zero n),
    have bad := eq.trans (eq.symm len_nil) x_len_fixed,
    contradiction,
cases y_l,
    have f : 0 ≠ n + 1 := ne.symm (nat.succ_ne_zero n),
    have bad := eq.trans (eq.symm len_nil) y_len_fixed,
    contradiction,
have head_xh : head (x_l_hd :: x_l_tl) = x_l_hd := rfl,
have head_yh : head (y_l_hd :: y_l_tl) = y_l_hd := rfl,
rw head_xh at x_fst_zero,
rw head_yh at y_fst_one,
simp [x_fst_zero, y_fst_one, sum_test, add_cons_cons 0 0 x_l_tl y_l_tl],
end

/-- the head of the sum of a vector and a point is 1 -/
lemma action_fst_fixed : ∀ x : aff_vec_coord_tuple K n, ∀ y : aff_pt_coord_tuple K n, head (x.1 + y.1) = 1 :=
    by {intros, simp only [eq.symm (head_action K n x y), x.3, y.3]; exact zero_add 1}

-- need to actually write out the function
@[ext]
def aff_group_action : aff_vec_coord_tuple K n → aff_pt_coord_tuple K n → aff_pt_coord_tuple K n :=
    λ x y, ⟨x.1 + y.1, list_action_fixed K n x y, action_fst_fixed K n x y⟩

@[ext]
instance : has_trans (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n) := ⟨aff_group_action K n⟩

lemma aff_zero_sadd : ∀ x : aff_pt_coord_tuple K n, (0 : aff_vec_coord_tuple K n) ⊹ x = x :=
begin
intro,
cases x,
have h₁ : (0 : aff_vec_coord_tuple K n) = ⟨field_zero K n, len_zero K n, head_zero K n⟩ := rfl,
rw h₁,
ext;
split,
{
    intro h,
    -- dsimp [has_trans.trans, aff_group_action],
    {sorry}
},
{sorry}
end

lemma aff_add_sadd : ∀ x y : aff_vec_coord_tuple K n, ∀ a : aff_pt_coord_tuple K n, (x + y) ⊹ a = x ⊹ y ⊹ a := sorry

instance : add_action (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n) := ⟨aff_zero_sadd K n, aff_add_sadd K n⟩

instance : add_space (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n) := add_space.mk

lemma aff_add_trans : ∀ a b : aff_pt_coord_tuple K n, ∃ x : aff_vec_coord_tuple K n, x ⊹ a = b := sorry

instance : add_homogeneous_space (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n) := ⟨aff_add_trans K n⟩

lemma aff_add_free : ∀ a : aff_pt_coord_tuple K n, ∀ g h : aff_vec_coord_tuple K n, g ⊹ a = h ⊹ a → g = h := sorry

instance aff_torsor : add_torsor (aff_vec_coord_tuple K n) (aff_pt_coord_tuple K n) := ⟨aff_add_free K n⟩
-- WTS the pair aff_vec_coord_tuple and aff_pt_coord_tuple form an affine space

instance aff_coord_is : affine_space (aff_pt_coord_tuple K n) K (aff_vec_coord_tuple K n) := aff_torsor K n
-- Different file, physical quantities
/-
def time' := space.mk 1
def geom3 := space.mk 2
def duration := aff_vec_coord_tuple ℝ 1 time'
def time     := aff_pt_coord_tuple  ℝ 1 time'
noncomputable def std_origin : time := ⟨[1, 0], rfl, rfl⟩
def length   := aff_vec_coord_tuple ℝ 3 geom3
def phys_pt  := aff_pt_coord_tuple  ℝ 3 geom3
-/
-- WTS the pair aff_vec_coord_tuple and aff_pt_coord_tuple form an affine space
instance aff_coord_inst : affine_space (aff_pt_coord_tuple K n) K (aff_vec_coord_tuple K n) := aff_torsor K n

inductive aff_frame 
| std_frame  --...
| new_frame (origin : aff_pt_coord_tuple K n) (vec : fin n → aff_vec_coord_tuple K n) (b : is_basis K vec) (old_frame : aff_frame)
