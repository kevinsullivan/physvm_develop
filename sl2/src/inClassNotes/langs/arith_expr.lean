/-
Define the abstract and concrete syntax and semantics of simple arithmetic expressions, to
include variables.
-/

inductive avar : Type
| mk (n : nat)

def a_state := avar → nat 

inductive aexp : Type 
| lit_expr (n : nat)
| var_expr (a : avar)
| add_expr (e1 e2 : aexp)
| mul_expr (e1 e2 : aexp)

open aexp

def aeval : aexp → a_state → nat 
| (lit_expr n) st := n
| (var_expr v) st :=  st v
| (add_expr e1 e2) st := (aeval e1 st) + (aeval e2 st)
| (mul_expr e1 e2) st := (aeval e1 st) * (aeval e2 st)

notation `[` n `]` := lit_expr n
notation `[` v `]` := var_expr v
notation e1 + e2 := add_expr e1 e2
notation e1 * e2 := mul_expr e1 e2

def st0 := λ (v : avar), 0
example : aeval ([3] + [5]) st0 = 8 := rfl 