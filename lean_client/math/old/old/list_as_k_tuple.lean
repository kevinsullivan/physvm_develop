import algebra.ring tactic.ext 

/-!
This file includes definitions of standard
coordinate tuples represented as lists and 
the usual coordinate-wise operations needed
for linear algebra. This file supports our
formalization of affine coordinate spaces. 
-/


universes u v
variables {k : Type u} [ring k] [inhabited k] {α : Type v} [has_add α]
(a b : α) (al bl : list α)
(x y : k) (xl yl : list k)
(n : ℕ)

open list

namespace vecl

def ladd : list α → list α → list α := zip_with has_add.add

/-- addition is compatible with list constructor -/
@[simp] theorem add_cons_cons (a b : α) (l₁ l₂ : list α) :
  ladd (a :: l₁) (b :: l₂) = (a + b) :: ladd l₁ l₂ := rfl

/-- adding the empty list to a list gives you the empty list -/
@[simp] theorem add_nil_left (l : list α) : ladd ([] : list α) l = [] := rfl

/-- adding a list to the empty list gives you the empty list -/
@[simp] theorem add_nil_right (l : list α) : ladd l ([] : list α) = [] :=
by cases l; refl


@[simp] theorem length_sum : ∀ (l₁ : list α) (l₂ : list α),
   length (ladd l₁ l₂) = min (length l₁) (length l₂)
| []      l₂      := rfl
| l₁      []      := by simp -- TODO: figure out which simp lemmata are being used, and use "simp only"
| (a::l₁) (b::l₂) := --by simp only [length, add_cons_cons, length_sum l₁ l₂, min_succ_succ]
begin
simp only [length, add_cons_cons, length_sum l₁ l₂],
exact ((length l₁).min_succ_succ (length l₂)).symm,
end

@[simp] theorem zip_with_cons_cons {α β γ} (f : α → β → γ) (a : α) (b : β) (l₁ : list α) (l₂ : list β) :
  list.zip_with f (a :: l₁) (b :: l₂) = f a b :: list.zip_with f l₁ l₂ := rfl

/-- the empty list is of length 0 -/
@[simp] lemma len_nil : length ([] : list α) = 0 := rfl
/-- every list is one longer than its tail -/
@[simp] lemma len_cons : length (a :: al) = length al + 1 := rfl

--! IMPORTANT: NO has_add INSTANCE ANYMORE

/-- may or may not need this -/
lemma ladd_defn : ladd al bl = (zip_with has_add.add) al bl := by {intros, refl}

/-- returns list of 0 vector of given length. -/
def zero_vector (k : Type*) [ring k] : ℕ → list k
| 0 := [0]
| (nat.succ n) := 0 :: (zero_vector n)

lemma field_zero_sep : ∀ n : ℕ, n ≠ 0 → zero_vector k n = 0 :: zero_vector k (n - 1) :=
begin
intros n h,
induction n with n',
{contradiction},
{refl}
end

/-- returns a list multiplied element-wise by a scalar. -/
def scalar_mul : k → list k → list k
| x [] := []
| x (a :: l) := (x * a) :: (scalar_mul x l)

/-- definitional lemmata for scalar_mul -/
lemma scalar_nil : scalar_mul x [] = [] := rfl
lemma scalar_cons : scalar_mul y (x :: xl) = (y * x) :: (scalar_mul y xl) := rfl

/-- scaling a vector does not change its length -/
lemma scale_len : length (scalar_mul x xl) = length xl := 
begin
induction xl,
rw scalar_nil,
simp only [scalar_cons, len_cons, xl_ih],
end

/-- scaling by 1 returns the original vector -/
lemma one_smul_cons : scalar_mul 1 xl = xl :=
begin
induction xl,
refl,
rw [scalar_cons, one_mul, xl_ih],
end

/-- scaling by 0 returns the zero vector -/
lemma zero_smul_cons : xl ≠ [] → scalar_mul 0 xl = zero_vector k (xl.length - 1) :=
begin
intros,
induction xl,
contradiction,
cases xl_tl,
have h₁ : scalar_mul 0 [xl_hd] = [0*xl_hd] := rfl,
have h₂ : zero_vector k ([xl_hd].length - 1) = [0] := rfl,
rw [h₁, h₂, zero_mul],

rw [scalar_cons, field_zero_sep],
have h₄ : (xl_hd :: xl_tl_hd :: xl_tl_tl).length - 1 - 1 = (xl_tl_hd :: xl_tl_tl).length - 1 := rfl,
rw [h₄, xl_ih, zero_mul],
repeat {contradiction},
end

/-- scaling the zero vector with anything returns the zero vector -/
lemma smul_zero_cons : scalar_mul x (zero_vector k n) = zero_vector k n :=
begin
induction n with n',
have h₁ : zero_vector k 0 = [0] := rfl,
have h₂ : scalar_mul x [0] = [x*0] := rfl,
rw [h₁, h₂, mul_zero],

have h₃ : n'.succ - 1 = n' := rfl,
rw [field_zero_sep, scalar_cons, mul_zero, h₃, n_ih],
contradiction
end

/-- scaling is consistent with ring multiplication -/
lemma smul_assoc : scalar_mul (x*y) xl = scalar_mul x (scalar_mul y xl) :=
begin
induction xl,
refl,
simp only [scalar_cons],
split,
rw mul_assoc,
exact xl_ih,
end

/-- neg function for rings -/
def ring_neg : k → k := λ a, -a
/-- neg function for lists -/
def vecl_neg : list k → list k := map ring_neg

lemma neg_cons : vecl_neg (x :: xl) = (-x) :: vecl_neg xl := rfl

/-- length of -x is the same as the length of x-/
@[simp] theorem len_neg : length (vecl_neg xl) = length xl := 
begin
induction xl,
{
    dsimp only [vecl_neg, ring_neg, map, length], refl,
},
{
  have t : vecl_neg (xl_hd :: xl_tl) = (-xl_hd :: vecl_neg xl_tl) := rfl,
  simp only [t, len_cons, xl_ih],
},
end

lemma ladd_assoc : ∀ x y z : list k, ladd (ladd x y) z = ladd x (ladd y z) :=
begin
intros x y z,
induction x generalizing y z,
simp only [add_nil_left, add_nil_right],
induction y generalizing z,
simp only [add_nil_left, add_nil_right],
cases z,
simp only [add_nil_left, add_nil_right],
rw ladd at x_ih y_ih ⊢,
repeat {rw zip_with_cons_cons},
rw add_assoc,
rw x_ih,
end

lemma zero_ladd : ∀ x : list k, ladd (zero_vector k (length x - 1)) x = x :=
begin
intro x,
induction x,
{refl},
{
  have tl_len : length (x_hd :: x_tl) - 1 = length x_tl := rfl,
  rw tl_len,
  induction x_tl,
  {
    have field_zero_zero : zero_vector k 0 = [0] := rfl,
    have add_list : ladd [0] [x_hd] = [0 + x_hd] := rfl,
    rw [len_nil, field_zero_zero, add_list, zero_add]
  },
  {
    have zero_tl : zero_vector k (length (x_tl_hd :: x_tl_tl)) = 0 :: zero_vector k (length x_tl_tl) :=
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
      have sep_head : ladd (0 :: (zero_vector k (length x_tl_tl))) (x_hd :: (x_tl_hd :: x_tl_tl)) =
        (0 + x_hd) :: ladd (zero_vector k (length x_tl_tl)) (x_tl_hd :: x_tl_tl) := rfl,
      have head_add : 0 + x_hd = x_hd := by rw zero_add,
      have len_x_tl : length x_tl_tl = length (x_tl_hd :: x_tl_tl) - 1 := rfl,
      rw [zero_tl, sep_head, head_add, len_x_tl, x_ih]
  }
}
end

lemma zero_ladd' : ∀ x : list k, ∀ n : ℕ, length x = n + 1 → ladd (zero_vector k n) x = x :=
begin
intros x n x_len,
induction x,
contradiction,
have tl_l : length (x_hd :: x_tl) - 1 = length x_tl := rfl,
have tl_len : length x_tl = n := nat.succ.inj x_len,
rw (eq.symm tl_len),
rw (eq.symm tl_l),
apply zero_ladd,
end 

lemma ladd_zero : ∀ x : list k, ladd x (zero_vector k (length x - 1)) = x :=
begin
intro x,
induction x,
{refl},
{
  have tl_len : length (x_hd :: x_tl) - 1 = length x_tl := rfl,
  rw tl_len,
  induction x_tl,
  {
    have field_zero_zero : zero_vector k 0 = [0] := rfl,
    have add_list : ladd [x_hd] [0] = [x_hd + 0] := rfl,
    rw [len_nil, field_zero_zero, add_list, add_zero]
  },
  {
    have zero_tl : zero_vector k (length (x_tl_hd :: x_tl_tl)) = 0 :: zero_vector k (length (x_tl_hd :: x_tl_tl) - 1) :=
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
    have sep_head : ladd (x_hd :: (x_tl_hd :: x_tl_tl)) (0 :: zero_vector k (length (x_tl_hd :: x_tl_tl) - 1)) =
      (x_hd + 0) :: ladd (x_tl_hd :: x_tl_tl) (zero_vector k (length (x_tl_hd :: x_tl_tl) - 1)) := rfl,
    have head_add : x_hd + 0 = x_hd := by rw add_zero,
    rw [zero_tl, sep_head, head_add, x_ih]
  }
}
end 

lemma ladd_zero' : ∀ x : list k, ∀ n : ℕ, length x = n + 1 → ladd x (zero_vector k n) = x :=
begin
intros x n x_len,
induction x,
contradiction,
have tl_l : length (x_hd :: x_tl) - 1 = length x_tl := rfl,
have tl_len : length x_tl = n := nat.succ.inj x_len,
rw (eq.symm tl_len),
rw (eq.symm tl_l),
apply ladd_zero,
end

lemma ladd_left_neg : ∀ x : list k, x ≠ [] → ladd (vecl_neg x) x = zero_vector k ((length x) - 1) :=
begin
intros x x_h,
induction x,
{contradiction},
{
  induction x_tl,
  {
    have neg_x : vecl_neg [x_hd] = [-x_hd] := rfl,
    have list_sum : ladd [-x_hd] [x_hd] = [-x_hd + x_hd] := rfl,
    have x_hd_sum : -x_hd + x_hd = 0 := by apply add_left_neg,
    have zero_is : zero_vector k (length [x_hd] - 1) = [0] := rfl,
    rw [neg_x, list_sum, x_hd_sum, zero_is],
  },
  {
    have neg_x : vecl_neg (x_hd :: x_tl_hd :: x_tl_tl) = (-x_hd) :: (vecl_neg (x_tl_hd :: x_tl_tl)) := rfl,
    have list_sum : ladd (-x_hd :: (vecl_neg (x_tl_hd :: x_tl_tl))) (x_hd :: x_tl_hd :: x_tl_tl) =
      (-x_hd + x_hd) :: ladd (vecl_neg (x_tl_hd :: x_tl_tl)) (x_tl_hd :: x_tl_tl) := rfl,
    have x_hd_sum : -x_hd + x_hd = 0 := by apply add_left_neg,
    have x_tl_sum : ladd (vecl_neg (x_tl_hd :: x_tl_tl)) (x_tl_hd :: x_tl_tl) = zero_vector k (length (x_tl_hd :: x_tl_tl) - 1) :=
      begin
      apply x_ih,
      contradiction
      end,
    have zero_is : zero_vector k (length (x_hd :: x_tl_hd :: x_tl_tl) - 1) = 0 :: zero_vector k (length (x_hd :: x_tl_tl) - 1) := rfl,
    rw [neg_x, list_sum, x_hd_sum, x_tl_sum, zero_is],
    refl,
  }
}
end

lemma ladd_comm : ∀ x y : list k, ladd x y = ladd y x :=
begin
intros l l',
  induction l with hd tl hl generalizing l',
  
  rw [add_nil_left, add_nil_right],
  
  cases l' with hd' tl',
  rw [add_nil_left, add_nil_right],
  rw ladd at hl ⊢,
  rw [zip_with_cons_cons, zip_with_cons_cons, hl, add_comm]
end

lemma ladd_free : ∀ (xl yl zl : list k), zl.length = xl.length → zl.length = yl.length → zl ≠ nil → ladd xl zl = ladd yl zl → xl = yl :=
begin
intros xl yl zl x_len y_len z_cons h₀,
have h₁ : ladd (ladd xl zl) (vecl_neg zl) = ladd (ladd yl zl) (vecl_neg zl) := by rw h₀,
repeat {rw ladd_assoc at h₁},
have h₂ : ladd zl (vecl_neg zl) = ladd (vecl_neg zl) zl := by rw ladd_comm,
have h₃ : xl.length = yl.length := eq.trans (eq.symm x_len) y_len,
rw [h₂, ladd_left_neg, x_len, ladd_zero, h₃, ladd_zero] at h₁,
exact h₁,
exact z_cons
end

lemma smul_ladd : scalar_mul x (ladd xl yl) = ladd (scalar_mul x xl) (scalar_mul x yl) :=
begin
induction xl generalizing yl,
refl,

cases yl,
refl,

rw [add_cons_cons, scalar_cons, scalar_cons, scalar_cons, add_cons_cons, left_distrib, xl_ih]
end

lemma ladd_smul : scalar_mul (x + y) xl = ladd (scalar_mul x xl) (scalar_mul y xl) :=
begin
induction xl,
refl,

repeat {rw scalar_cons},
rw [add_cons_cons, right_distrib, xl_ih]
end

#check zip_with

end vecl