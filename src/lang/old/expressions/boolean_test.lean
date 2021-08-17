import .boolean

def init_benv : benv := λ v, ff

def myFirstProg := bCmd.bAssm (bvar.mk 0) (bExpr.BLit ff)

def newEnv := cEval init_benv myFirstProg

#eval newEnv (bvar.mk 0)