import .lang.imperative_DSL.physlang

noncomputable theory

def env4 := init_env


def worldGeometry := cmd.classicalGeometryAssmt (lang.classicalGeometry.var.mk 1) (lang.classicalGeometry.expr.lit(classicalGeometry.mk 1 3))

 def env5 := cmdEval worldGeometry env4


def worldTime := cmd.classicalTimeAssmt (lang.classicalTime.var.mk 3) (lang.classicalTime.expr.lit(classicalTime.mk 2))

 def env6 := cmdEval worldTime env5

def INDEX104809424.STMTCOMMAND.B.L97C32.E.L110C1 : cmd :=(cmd.seq worldTime worldGeometry)

