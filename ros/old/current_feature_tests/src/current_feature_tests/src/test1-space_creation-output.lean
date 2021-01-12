import .lang.imperative_DSL.physlang

noncomputable theory

def env11 := environment.init_env


def worldGeometry := cmd.classicalGeometryAssmt (lang.classicalGeometry.var.mk 2) (lang.classicalGeometry.expr.lit(classicalGeometry.mk 2 3))

 def env12 := cmdEval worldGeometry env11


def worldTime := cmd.classicalTimeAssmt (lang.classicalTime.var.mk 4) (lang.classicalTime.expr.lit(classicalTime.mk 3))

 def env13 := cmdEval worldTime env12


def worldVelocity := cmd.classicalVelocityAssmt 
		(lang.classicalVelocity.var.mk 6) 
		(lang.classicalVelocity.expr.lit (classicalVelocity.mk 5 
			(classicalGeometryEval (lang.classicalGeometry.expr.var (lang.classicalGeometry.var.mk 2)) ( env13 )) 
			(classicalTimeEval (lang.classicalTime.expr.var (lang.classicalTime.var.mk 4)) ( env13 ))))

 def env14 := cmdEval worldVelocity env13


def worldAcceleration := cmd.classicalAccelerationAssmt 
		(lang.classicalAcceleration.var.mk 8) 
		(lang.classicalAcceleration.expr.lit (classicalAcceleration.mk 7 
			(classicalVelocityEval (lang.classicalVelocity.expr.var (lang.classicalVelocity.var.mk 6)) ( env14 )) 
			(classicalTimeEval (lang.classicalTime.expr.var (lang.classicalTime.var.mk 4)) ( env14 ))))

 def env15 := cmdEval worldAcceleration env14

def INDEX116082464.STMTCOMMAND.B.L36C32.E.L46C1 : cmd :=(cmd.seq worldAcceleration (cmd.seq worldVelocity (cmd.seq worldTime worldGeometry)))

