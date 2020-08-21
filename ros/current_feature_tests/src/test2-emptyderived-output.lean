import .lang.imperative_DSL.physlang

noncomputable theory

def env7 := init_env


def worldGeometry := cmd.classicalGeometryAssmt (lang.classicalGeometry.var.mk 1) (lang.classicalGeometry.expr.lit(classicalGeometry.mk 1 3))

 def env8 := cmdEval worldGeometry env7


def worldTime := cmd.classicalTimeAssmt (lang.classicalTime.var.mk 3) (lang.classicalTime.expr.lit(classicalTime.mk 2))

 def env9 := cmdEval worldTime env8


def worldVelocity := cmd.classicalVelocityAssmt 
		(lang.classicalVelocity.var.mk 5) 
		(lang.classicalVelocity.expr.lit (classicalVelocity.mk 4 
			(lang.classicalGeometry.eval (lang.classicalGeometry.expr.var (lang.classicalGeometry.var.mk 1)) (classicalGeometryGet env9) ) 
			(lang.classicalTime.eval (lang.classicalTime.expr.var (lang.classicalTime.var.mk 3)) (classicalTimeGet env9) )))

 def env10 := cmdEval worldVelocity env9

def INDEX104809424.STMTCOMMAND.B.L97C32.E.L110C1 : cmd :=(cmd.seq worldVelocity (cmd.seq worldTime worldGeometry))

