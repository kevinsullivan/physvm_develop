/-
true, 
false, 
true && false, 
(true && false) && true
-/
inductive bool_expr : Type
| lit_expr : bool → bool_expr 
| and_expr : bool_expr → bool_expr → bool_expr 
| or_expr : bool_expr → bool_expr → bool_expr
| not_expr : bool_expr → bool_expr

open bool_expr 

notation e1 && e2 := and_expr e1 e2
notation `[` b `]` := lit_expr b
notation e1 ∨ e2 := or_expr e1 e2
notation ¬e1 := not_expr e1

def true_expr : bool_expr := [tt]
def false_expr : bool_expr := [ff]
def e3 := and_expr (lit_expr tt) [ff]
def e4 := and_expr e3 [tt]

notation e1 && e2 := and_expr e1 e2

def e3' := [tt] && [ff]
def e4' := e3 && [tt]


-- That's the syntax

-- Now for the semantics

#check eq.cases_on

def bool_eval : bool_expr → bool
| (lit_expr b) := b
| (and_expr e1 e2) := band (bool_eval e1) (bool_eval e2)
| (or_expr e1 e2) := bor (bool_eval e1) (bool_eval e2)
| (not_expr e1) := ¬(bool_eval e1)

lemma bool_eval_and_expr_comm : ∀e1 e2 : bool_expr, (bool_eval (e1 && e2)) == (bool_eval (e2 && e1)) :=
begin
  intros,
  let band_comm : ∀b1 b2 : bool, b1 && b2 == b2 && b1 := 
    begin
      intros,
      cases b1, 
      cases b2,
      repeat {simp [band]},
    end,
  simp [bool_eval],
  exact band_comm _ _
end

#eval bool_eval e4'