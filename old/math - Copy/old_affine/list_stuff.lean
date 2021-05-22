import algebra.field tactic.ext
open list

universes u v
variables (K : Type u) [field K] [inhabited K] {α : Type v} [has_add α]
(x y : K) (xl yl : list K)

/-- addition function on `list α`, where `α` has an addition function -/
@[ext]
def ladd : list α → list α → list α := zip_with has_add.add

/- 
    The following theorems are stolen from data.list.zip and adapted for the zip_with function, which is
    more generic than the zip function the lemmata were initially used for. These lemmata are used in the
    file aff_coord_space to prove statements necessary to show aff_vec_coord_tuple is a vector space. 
-/

/-- addition is compatible with list constructor -/
@[simp] theorem add_cons_cons (a b : α) (l₁ l₂ : list α) :
  ladd (a :: l₁) (b :: l₂) = (a + b) :: ladd l₁ l₂ := rfl

/-- adding the empty list to a list gives you the empty list -/
@[simp] theorem add_nil_left (l : list α) : ladd ([] : list α) l = [] := rfl

/-- adding a list to the empty list gives you the empty list -/
@[simp] theorem add_nil_right (l : list α) : ladd l ([] : list α) = [] :=
by cases l; refl


/-- The length of the sum of two lists is the length of the shorter list -/
@[simp] theorem length_sum : ∀ (l₁ : list α) (l₂ : list α),
   length (ladd l₁ l₂) = min (length l₁) (length l₂)
| []      l₂      := rfl
| l₁      []      := by simp -- TODO: figure out which simp lemmata are being used, and use "simp only"
| (a::l₁) (b::l₂) := --by simp only [length, add_cons_cons, length_sum l₁ l₂, min_succ_succ]
begin
simp only [length, add_cons_cons, length_sum l₁ l₂],
exact ((length l₁).min_succ_succ (length l₂)).symm,
end


/-- the length of nil is 0 -/
lemma len_nil : length ([] : list α) = 0 := rfl

lemma len_cons : length (x :: xl) = length xl + 1 := rfl

/-- Implements list addition coordinate-wise w.r.t. the addition function on the list entries. -/
instance (α : Type*) [has_add α] : has_add (list α) := ⟨ladd⟩

-- TODO: rename this lemma. It's actually important
lemma sum_test : ∀ a b : list K, a + b = ladd a b := by {intros, refl}

lemma sum_test' : ∀ a b : list K, a + b = (zip_with has_add.add) a b := by {intros, refl}

/-- returns list rep of 0 vector of given length. -/
def list.field_zero : ℕ → list K
| 0 := [0]
| (nat.succ n) := 0 :: (list.field_zero n)

/-- returns a list multiplied element-wise by a scalar. -/
def list.field_scalar : K → list K → list K
| x [] := []
| x (a :: l) := (x * a) :: (list.field_scalar x l)


lemma scalar_nil : list.field_scalar K x [] = [] := rfl

lemma scalar_cons : list.field_scalar K y (x :: xl) = (y * x) :: (list.field_scalar K y xl) := rfl

lemma scale_len : length (list.field_scalar K x xl) = length xl := 
begin
induction xl,
rw scalar_nil,
simp only [scalar_cons, len_cons, xl_ih],
end

lemma list.one_smul_cons : list.field_scalar K 1 xl = xl :=
begin
induction xl,
refl,
rw [scalar_cons, one_mul, xl_ih],
end

lemma list.smul_assoc : list.field_scalar K (x*y) xl = list.field_scalar K x (list.field_scalar K y xl) :=
begin
induction xl,
refl,
simp only [scalar_cons],
split,
rw mul_assoc,
exact xl_ih,
end

lemma list.smul_zero : ∀ n : ℕ, list.field_scalar K x (list.field_zero K n) = list.field_zero K n :=
begin
intros,
induction n with n',
{
  have zero_is : list.field_zero K 0 = [0] := rfl,
  have mul_zero : x * 0 = 0 := by apply mul_zero,
  rw [zero_is, scalar_cons, mul_zero, scalar_nil]
},
{
  have field_zero_succ : list.field_zero K n'.succ = 0 :: list.field_zero K n' := rfl,
  have mul_zero : x * 0 = 0 := by apply mul_zero,
  rw [field_zero_succ, scalar_cons, mul_zero, n_ih]
}
end

lemma list.zero_smul : xl ≠ nil → list.field_scalar K 0 xl = list.field_zero K (length xl - 1) :=
begin
intro h,
induction xl,
{contradiction},
{
  induction xl_tl,
  {
    have zero_is : list.field_zero K ([xl_hd].length - 1) = [0] := rfl,
    have zero_mul : 0 * xl_hd = 0 := by apply zero_mul,
    rw [zero_is, scalar_cons, scalar_nil, zero_mul]
  },
  {
    have zero_mul : 0 * xl_hd = 0 := by apply zero_mul,
    have non_nil : xl_tl_hd :: xl_tl_tl ≠ nil := by contradiction,
    rw [scalar_cons, zero_mul, xl_ih non_nil],
    refl
  }
}
end

--below are functions. TODO: remove 2 of the neg functions

def field_neg : K → K := λ a, -a

def list.neg : list K → list K := map (field_neg K)

def list.neg' : list K → list K := λ x, list.field_scalar K (-1 : K) x

def list.neg'' : list K → list K
| [] := []
| (x :: xl) := (-x) :: list.neg'' xl

lemma neg_cons : list.neg K (x :: xl) = (-x) :: list.neg K xl := rfl

lemma neg_nil_nil : list.neg K nil = nil := rfl

lemma len_succ : ∀ a : α, ∀ al : list α, length (a :: al) = length al + 1 := by intros; refl

@[simp] theorem list.len_neg : length (list.neg K xl) = length xl := 
begin
induction xl,
{
  rw neg_nil_nil
},
{
  have t : list.neg K (xl_hd :: xl_tl) = (-xl_hd :: list.neg K xl_tl) := rfl,
  simp only [t, len_succ, xl_ih],
},
end

lemma field_zero_sep : ∀ n : ℕ, n ≠ 0 → list.field_zero K n = 0 :: list.field_zero K (n - 1) :=
begin
intros n h,
induction n with n',
{contradiction},
{refl}
end

-- Lemmas concerning addition
lemma list.ladd_is : ∀ x y : list K, ladd x y = x + y := by {intros, refl}

lemma nil_add : ∀ x : list K, nil + x = nil := by {intros, refl}
lemma add_nil : ∀ x : list K, x + nil = nil := by {intros, induction x, refl, refl}

lemma list.add_assoc : ∀ x y z : list K, (x + y) + z = x + (y + z) :=
begin
intros x y z,
cases x, refl,
cases y, refl,
cases z, refl,
sorry,
end

lemma list.zero_add : ∀ x : list K, (list.field_zero K (length x - 1)) + x = x :=
begin
intro x,
induction x,
{refl},
{
  have tl_len : length (x_hd :: x_tl) - 1 = length x_tl := rfl,
  rw tl_len,
  induction x_tl,
  {
    have field_zero_zero : list.field_zero K 0 = [0] := rfl,
    have add_list : [0] + [x_hd] = [0 + x_hd] := rfl,
    rw [len_nil, field_zero_zero, add_list, zero_add]
  },
  {
    have zero_tl : list.field_zero K (length (x_tl_hd :: x_tl_tl)) = 0 :: list.field_zero K (length x_tl_tl) :=
      begin
      have len_x : length (x_tl_hd :: x_tl_tl) ≠ 0 :=
        begin
        intro h,
        have len_x' : length (x_tl_hd :: x_tl_tl) = length x_tl_tl + 1 := rfl,
        contradiction
        end,
      apply field_zero_sep,
      exact len_x
      end,
      have sep_head : 0 :: list.field_zero K (length x_tl_tl) + x_hd :: (x_tl_hd :: x_tl_tl) =
        (0 + x_hd) :: (list.field_zero K (length x_tl_tl) + (x_tl_hd :: x_tl_tl)) := rfl,
      have head_add : 0 + x_hd = x_hd := by rw zero_add,
      have len_x_tl : length x_tl_tl = length (x_tl_hd :: x_tl_tl) - 1 := rfl,
      rw [zero_tl, sep_head, head_add, len_x_tl, x_ih]
  }
}
end

lemma list.zero_add' : ∀ x : list K, ∀ n : ℕ, length x = n + 1 → (list.field_zero K n) + x = x :=
begin
intros x n x_len,
induction x,
contradiction,
have tl_l : length (x_hd :: x_tl) - 1 = length x_tl := rfl,
have tl_len : length x_tl = n := nat.succ.inj x_len,
rw (eq.symm tl_len),
rw (eq.symm tl_l),
apply list.zero_add,
end 

-- TODO: clean up this lemma
lemma list.add_zero : ∀ x : list K, x + (list.field_zero K (length x - 1)) = x :=
begin
intro x,
induction x,
{refl},
{
  have tl_len : length (x_hd :: x_tl) - 1 = length x_tl := rfl,
  rw tl_len,
  induction x_tl,
  {
    have field_zero_zero : list.field_zero K 0 = [0] := rfl,
    have add_list : [x_hd] + [0] = [x_hd + 0] := rfl,
    rw [len_nil, field_zero_zero, add_list, add_zero]
  },
  {
    have zero_tl : list.field_zero K (length (x_tl_hd :: x_tl_tl)) = 0 :: list.field_zero K (length (x_tl_hd :: x_tl_tl) - 1) :=
      begin
      have len_x : length (x_tl_hd :: x_tl_tl) ≠ 0 :=
        begin
        intro h,
        have len_x' : length (x_tl_hd :: x_tl_tl) = length x_tl_tl + 1 := rfl,
        contradiction
        end,
      apply field_zero_sep,
      exact len_x
      end,
    have sep_head : x_hd :: (x_tl_hd :: x_tl_tl) + 0 :: list.field_zero K (length (x_tl_hd :: x_tl_tl) - 1) =
      (x_hd + 0) :: ((x_tl_hd :: x_tl_tl) + list.field_zero K (length (x_tl_hd :: x_tl_tl) - 1)) := rfl,
    have head_add : x_hd + 0 = x_hd := by rw add_zero,
    rw [zero_tl, sep_head, head_add, x_ih]
  }
}
end

lemma list.add_zero' : ∀ x : list K, ∀ n : ℕ, length x = n + 1 → x + (list.field_zero K n) = x :=
begin
intros x n x_len,
induction x,
contradiction,
have tl_l : length (x_hd :: x_tl) - 1 = length x_tl := rfl,
have tl_len : length x_tl = n := nat.succ.inj x_len,
rw (eq.symm tl_len),
rw (eq.symm tl_l),
apply list.add_zero,
end

lemma list.add_left_neg : ∀ x : list K, x ≠ [] → list.neg K x + x = list.field_zero K ((length x) - 1) :=
begin
intros x x_h,
induction x,
/-
This theorem won't work if x = []
-x + x = -[] + [] = []
length x - 1 = 0 - 1 = 0 (because 0 is a ℕ)
list.field_zero K 0 = [0]
[] ≠ [0]
-/
{contradiction},
{
  induction x_tl,
  {
    have neg_x : list.neg K [x_hd] = [-x_hd] := rfl,
    have list_sum : [-x_hd] + [x_hd] = [-x_hd + x_hd] := rfl,
    have x_hd_sum : -x_hd + x_hd = 0 := by apply add_left_neg,
    have zero_is : list.field_zero K (length [x_hd] - 1) = [0] := rfl,
    rw [neg_x, list_sum, x_hd_sum, zero_is]
  },
  {
    have neg_x : list.neg K (x_hd :: x_tl_hd :: x_tl_tl) = (-x_hd) :: (list.neg K (x_tl_hd :: x_tl_tl)) := rfl,
    have list_sum : -x_hd :: list.neg K (x_tl_hd :: x_tl_tl) + x_hd :: x_tl_hd :: x_tl_tl =
      (-x_hd + x_hd) :: (list.neg K (x_tl_hd :: x_tl_tl) + x_tl_hd :: x_tl_tl) := rfl,
    have x_hd_sum : -x_hd + x_hd = 0 := by apply add_left_neg,
    have x_tl_sum : list.neg K (x_tl_hd :: x_tl_tl) + x_tl_hd :: x_tl_tl = list.field_zero K (length (x_tl_hd :: x_tl_tl) - 1) :=
      begin
      apply x_ih,
      contradiction
      end,
    have zero_is : list.field_zero K (length (x_hd :: x_tl_hd :: x_tl_tl) - 1) = 0 :: list.field_zero K (length (x_hd :: x_tl_tl) - 1) := rfl,
    rw [neg_x, list_sum, x_hd_sum, x_tl_sum, zero_is],
    refl
  }
}
end

lemma head_cons_add : ∀ a : K, ∀ x y : list K, a :: x + y = a :: (x + y) := sorry

lemma list.add_comm : ∀ x y : list K, x + y = y + x :=
begin
intros x y,
cases x,
dsimp only [has_add.add],
rw [add_nil_left, add_nil_right],
sorry,
end

lemma list.add_trans : ∀ a b : list K, length a = length b → ∃ x : list K, x + a = b :=
begin
intros a b h,
induction a,
{
  apply exists.intro,
  {
    have b_nil : b = nil := by {cases b, refl, contradiction},
    rw [b_nil, add_nil]
  },
  {exact nil}
},
{
  apply exists.intro,
  {
    induction b,
    {contradiction},
    {sorry}
  },
  {exact b + list.neg K (a_hd :: a_tl)}
}
end

lemma list.aff_add_trans : ∀ a b : list K, (length a = length b) ∧ (a.head = (1 : K)) ∧ (b.head = (1 : K)) → ∃ x : list K, (x + a = b ∧ x.head = (0 : K)) :=
begin
sorry
end

lemma list.add_free : ∀ a g h : list K, length g = length a → length h = length a → g + a = h + a → g = h :=
begin
intros a g h g_len_a h_len_a sum_h,
cases a,
{
  have g_nil : g = nil := by {cases g, refl, contradiction},
  have h_nil : h = nil := by {cases h, refl, contradiction},
  rw [g_nil, h_nil]
},
{
  have g_neg_cancel : g = g + (a_hd :: a_tl) + list.neg K (a_hd :: a_tl) :=
  begin
    have a_na_zero : (a_hd :: a_tl) + list.neg K (a_hd :: a_tl) = list.field_zero K ((length (a_hd :: a_tl)) - 1) :=
    begin
      transitivity,
      {apply list.add_comm},
      {
        apply list.add_left_neg,
        have a_not_nil : (a_hd :: a_tl) ≠ nil := by contradiction,
        apply a_not_nil
      }
    end,
    rw [list.add_assoc, a_na_zero],
    rw [eq.symm g_len_a],
    symmetry,
    apply list.add_zero
  end,
  have h_neg_cancel : h = h + (a_hd :: a_tl) + list.neg K (a_hd :: a_tl) :=
  begin
    have a_na_zero : (a_hd :: a_tl) + list.neg K (a_hd :: a_tl) = list.field_zero K ((length (a_hd :: a_tl)) - 1) :=
    begin
      transitivity,
      {apply list.add_comm},
      {
        apply list.add_left_neg,
        have a_not_nil : (a_hd :: a_tl) ≠ nil := by contradiction,
        apply a_not_nil
      }
    end,
    rw [list.add_assoc, a_na_zero],
    rw [eq.symm h_len_a],
    symmetry,
    apply list.add_zero
  end,
rw [g_neg_cancel, h_neg_cancel, sum_h]
}
end

-- Lemmas that involve addition and scalar multiplication
lemma list.smul_add : ∀ g : K, ∀ x y : list K, list.field_scalar K g (x + y) = (list.field_scalar K g x) + (list.field_scalar K g y) :=
begin
intros,
induction x,
{
  rw [nil_add, scalar_nil, nil_add]
},
{
  induction y,
  {rw [scalar_nil, add_nil, add_nil, scalar_nil]},
  {
    repeat {rw scalar_cons},
    have add_xy : x_hd :: x_tl + y_hd :: y_tl = (x_hd + y_hd) :: (x_tl + y_tl) := rfl,
    have scalar_is : g * x_hd :: list.field_scalar K g x_tl + g * y_hd :: list.field_scalar K g y_tl = (g * x_hd + g * y_hd) :: (list.field_scalar K g x_tl + list.field_scalar K g y_tl) := rfl,
    have head_distrib : g * x_hd + g * y_hd = g * (x_hd + y_hd) := by {symmetry, apply left_distrib},
    have tail_distrib : list.field_scalar K g x_tl + list.field_scalar K g y_tl = list.field_scalar K g (x_tl + y_tl) := sorry,
    rw [add_xy, scalar_cons, scalar_is, head_distrib, tail_distrib]
  }
}
end

lemma list.add_smul : ∀ g h : K, ∀ x : list K, list.field_scalar K (g + h) x = (list.field_scalar K g x) + (list.field_scalar K h x) :=
begin
intros,
induction x,
{
  rw [scalar_nil, scalar_nil, scalar_nil],
  refl
},
{
  have sum_is : g * x_hd :: list.field_scalar K g x_tl + h * x_hd :: list.field_scalar K h x_tl = (g * x_hd + h * x_hd) :: (list.field_scalar K g x_tl + list.field_scalar K h x_tl) := rfl,
  have head_distrib : g * x_hd + h * x_hd = (g + h) * x_hd := by {symmetry, apply right_distrib},
  rw [scalar_cons, scalar_cons, scalar_cons, sum_is, head_distrib, x_ih]
}
end