/-
A total function
-- set theoretic representation of the squaring function
sqr : ℕ → ℕ := { (0,0), (1,1), (2,4), (3,9), ... }
-/


/-
Computational representation of the function
-/
def sqr : ℕ → ℕ := λ n, n*n
#eval sqr 3


/-
Logical, declarative, predicate that defines the same function
-/
inductive sqr_pred : ℕ → ℕ → Prop 
| in_sqr_pred : ∀ (n1 n2 : ℕ), (n2 = n1 * n1) → sqr_pred n1 n2

-- h === in_sqr_pred n1 n2 k

theorem verification : ∀ (n1 n2 : ℕ), sqr_pred n1 n2 → sqr n1 = n2 := 
begin
  assume n1 n2,
  assume h,
  cases h,
  unfold sqr,
  apply eq.symm _,
  assumption,
end

-- 

#check sqr_pred
#check sqr_pred 3 8 

open sqr_pred

-- explicit proof term
example : sqr_pred 3 9 := in_sqr_pred 3 9 (eq.refl 9)

example : sqr_pred 4 16 := in_sqr_pred _ _ (eq.refl _)

example : sqr_pred 3 9 := 
begin
  apply in_sqr_pred _ _ _,
  exact eq.refl _,
end

example : sqr_pred 4 16 := 
begin
  apply in_sqr_pred _ _ _,
  exact eq.refl _,
end

example : sqr_pred 3 15 := in_sqr_pred _ _ (eq.refl _)


/-
sqr_ev : ℕ → ℕ := { (0,0), (2,4), (4,16), ... }
-/

def evn : ℕ → bool := λ n, n%2 = 0

inductive sqr_ev_pred : ℕ → ℕ → Prop 
| in_sqr_ev_pred : ∀ (n1 n2 : ℕ),  (n1%2 = 0) → (n2 = n1 * n1) → sqr_ev_pred n1 n2

open sqr_ev_pred

example : sqr_ev_pred 4 16 := 
begin
  apply in_sqr_ev_pred,
  apply eq.refl _,
  apply eq.refl 16,
end

example : sqr_ev_pred 3 9 := 
begin
  apply in_sqr_ev_pred,
  apply eq.refl _, -- stuck
end







