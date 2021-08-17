/-
We have a better version of this. To be replaced.
-/

inductive bvar : Type
| mk (n : ℕ)

def bvar_eq : bvar → bvar → bool
| (bvar.mk n1) (bvar.mk n2) := n1=n2

inductive bExpr : Type
| BLit (b: bool)
| BVar (v: bvar)

def benv := bvar → bool

def bEval : bExpr → benv → bool
| (bExpr.BLit b) i := b
| (bExpr.BVar v) i := i v

def update_benv : benv → bvar → bool → benv 
| i v b := λ v2, if (bvar_eq v v2) then b else (i v2)

inductive bCmd : Type
| bAssm (v : bvar) (e : bExpr)
| bSeq (c1 c2 : bCmd)

def cEval : benv → bCmd → benv 
| i0 (bCmd.bAssm v e)  := update_benv i0 v (bEval e i0)
| i0 (bCmd.bSeq c1 c2) := (cEval (cEval i0 c1) c2)