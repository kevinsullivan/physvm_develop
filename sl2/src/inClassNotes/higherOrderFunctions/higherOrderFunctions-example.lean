def func (n : nat) : (nat → nat) :=
  λ (m : ℕ), m + n 

def foo (n : nat) : (nat → (string → bool)) :=
fun (m : nat), 
  fun (s : string),
    tt

#check foo 1 2 

#check foo

def x := func 3

#check func 

-- func 3
-- λ (m : ℕ), 3 + m
-- x := λ (m : ℕ), 3 + m

#eval x 6
-- 3 + m
-- 3 + 6
-- 9

/-
def func (3 : nat) : (nat → nat) :=
  fun (m : ℕ), m + 1
-/

/-
6 + 1
-/

-- ℕ → (ℕ → ℕ)
#check nat.add

/-
def func (n : nat) : (nat → nat) :=
  λ (m : ℕ), n + m 
-/

-- func 5
-- λ (m : ℕ), 5 + m

#eval (λ (m : ℕ), 5 + m) 7
-- 5 + m
-- 5 + 7
-- 12