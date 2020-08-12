/- DEMO -/

inductive bvar : Type
| mk (n : ℕ)

def bvar_eq : bvar → bvar → bool
| (bvar.mk n1) (bvar.mk n2) := n1=n2

inductive bExpr : Type
|BLit (b: bool)
|BVar (v: bvar)

-- An environment is a function from bvar to bool

def benv := bvar → bool

def bEval : bExpr → benv → bool
| (bExpr.BLit b) i := b
| (bExpr.BVar v) i := i v


def init_benv : benv := λ v, ff

def update_benv : benv → bvar → bool → benv 
| e v b := λ v2, if (bvar_eq v v2) then b else (e v2)

inductive bCmd : Type
| bSkip
| bAssm (v : bvar) (e : bExpr)
| bSeq (c1 c2 : bCmd)
| bIf (b : bool) (c1 c2 : bCmd)

def cEval : benv → bCmd → benv 
| i0 c :=   match c with
            | bCmd.bSkip := i0
            | (bCmd.bAssm v e) := update_benv i0 v (bEval e i0)
            | (bCmd.bSeq c1 c2) := 
                begin
                    have i1 := cEval i0 c1,
                    have i2 := cEval i1 c2,
                    exact i0, -- exact i2,
                end
                -- let i1 := (cEval i0 c1) in
                --  (cEval i1 c2)
            | (bCmd.bIf b c1 c2) := match b with 
                | tt := i0 --cEval i0 c1
                | ff := i0 --cEval i0 c2
                end
            end

def myFirstProg := bCmd.bAssm (bvar.mk 0) (bExpr.BLit ff)

def newEnv := cEval init_benv myFirstProg

#eval newEnv (bvar.mk 0) 