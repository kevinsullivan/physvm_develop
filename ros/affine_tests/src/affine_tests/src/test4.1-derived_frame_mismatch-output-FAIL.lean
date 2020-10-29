/-

A Euclidean Geometry 3-space is created.
The standard frame on the space is referenced and assigned to a variable.
A derived frame is created in terms of standard frame.
A point is constructed using the derived frame. 
A point is constructed using the standard frame.
These points are subtracted one another. 
A type error occurs due to the differing frames.

-/

import .lang.imperative_DSL.physlang

noncomputable theory

def env7 := init_env


def worldGeometry := cmd.classicalGeometryAssmt (lang.classicalGeometry.var.mk 1) (lang.classicalGeometry.expr.lit(classicalGeometry.mk 1 3))

 def env8 := cmdEval worldGeometry env7

def stdWorldFrame := cmd.classicalGeometryFrameAssmt (lang.classicalGeometry.frame_var.mk 11) (lang.classicalGeometry.getStdFrame (classicalGeometryEval (lang.classicalGeometry.expr.var (lang.classicalGeometry.var.mk 1)) ( env8 )))

def env9 := cmdEval worldGeometry.stdFrame env8

def worldTime := cmd.classicalTimeAssmt (lang.classicalTime.var.mk 3) (lang.classicalTime.expr.lit(classicalTime.mk 2))

def env10 := cmdEval worldTime env9

----def worldTime.stdFrame := cmd.classicalGeometryFrameAssmt (lang.classicalGeometry.frame_var.mk 12) (lang.classicalTime.getStdFrame (classicalTimeEval (lang.classicalTime.expr.var (lang.classicalTime.var.mk 2)) ( env10 )))

def env11 := cmdEval worldTime.stdFrame env10

def worldVelocity := cmd.classicalVelocityAssmt 
		(lang.classicalVelocity.var.mk 5) 
		(lang.classicalVelocity.expr.lit (classicalVelocity.mk 4 
			(lang.classicalGeometry.eval (lang.classicalGeometry.expr.var (lang.classicalGeometry.var.mk 1)) (classicalGeometryGet env9) ) 
			(lang.classicalTime.eval (lang.classicalTime.expr.var (lang.classicalTime.var.mk 3)) (classicalTimeGet env9) )))

def env12 := cmdEval worldVelocity env11

--def worldVelocity.stdFrame := cmd.classicalVelocityFrameAssmt (lang.classicalVelocity.frame_var.mk 13) (lang.classicalVelocity.getStdFrame (classicalVelocityEval (lang.classicalVelocity.expr.var (lang.classicalVelocity.var.mk 2)) ( env12 )))

def env13 := cmdEval  worldVelocity.stdFrame env12

def INDEX104809424.STMTCOMMAND.B.L97C32.E.L110C1 : cmd :=(cmd.seq worldVelocity cmd.seq(cmd.seq worldTime (cmd.seq worldGeometry worldGeometry.stdFrame)))

