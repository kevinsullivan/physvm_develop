inductive bool_var : Type
| mk (n : nat)

open bool_var

/-
Abstract syntax
-/
inductive bool_expr : Type
| lit_expr : bool → bool_expr 
| var_expr : bool_var → bool_expr
| and_expr : bool_expr → bool_expr → bool_expr 
| or_expr : bool_expr → bool_expr → bool_expr 
| impl_expr : bool_expr → bool_expr → bool_expr   -- New
| not_expr : bool_expr → bool_expr 

open bool_expr 

/-
Concrete syntax
-/
notation e1 ∧ e2 := and_expr e1 e2
notation e1 ∨ e2 := or_expr e1 e2
notation ¬e := not_expr e
notation `[` b `]` := lit_expr b
notation `[` v `]` := var_expr v
reserve infixr `=>`:67                          -- New
notation e1 => e2 := impl_expr e1 e2            -- New    

/-
Semantics
-/

-- Boolean implies function, not provided by Lean
def bimp : bool → bool → bool 
| tt ff := ff
| _ _ := tt

def bool_eval : bool_expr → (bool_var → bool) → bool
| (lit_expr b) _ := b
| (var_expr v) st := st v 
| (and_expr e1 e2) st := band (bool_eval e1 st) (bool_eval e2 st)
| (or_expr e1 e2) st := bor (bool_eval e1 st) (bool_eval e2 st)
| (impl_expr e1 e2) st := bimp (bool_eval e1 st) (bool_eval e2 st) -- New
| (not_expr e) st := bnot (bool_eval e st)

/-
Testing -- traditional, run program, compare to expected output
-/

def true_expr : bool_expr := [tt]
def false_expr : bool_expr := [ff]
def e1 := [tt] ∧ [ff]
def e2 := e1 ∨  [tt]

-- Let's name some variables

def Pvar := (bool_var.mk 0)
def Qvar := (bool_var.mk 1)
def Rvar := (bool_var.mk 2)

-- One possible state: giving values to variables
def bool_state_4 : bool_var → bool :=
λ v, 
match v with
  | (bool_var.mk 0) := tt
  | (bool_var.mk 1) := ff
  | (bool_var.mk 2) := ff
  | _ := ff
  end

/-
Informal testing: run code, compare actual to expected output
-/
#eval bool_eval e2 bool_state_4  -- expect tt

/-
Testing as proving theorems about specific inputs (not ∀ propositions)
-/
example : bool_eval e2 bool_state_4 = tt := rfl
example : bool_eval (¬e2 ∨ e1) bool_state_4 = ff := rfl

-- An expression with variable expressions as subexpressions
def e5' := [Pvar] ∧ [Qvar]

/-
Properties
-/

-- Oops, this proof broke when we added state as an argument

theorem and_connective_commutes : ∀ (e1 e2 : bool_expr), 
  bool_eval (e1 ∧ e2) = bool_eval (e2 ∧ e1) 
  :=
begin
  assume e1 e2,
  simp [bool_eval],
  cases (bool_eval e1),
  cases (bool_eval e2),
  apply rfl,
  apply rfl,
  cases (bool_eval e2),
  repeat {apply rfl},
end


