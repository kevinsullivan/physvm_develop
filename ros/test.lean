import .lang.imperative_DSL.physlang

noncomputable theory



def klkkvar : lang.classicalGeometry.var := lang.classicalGeometry.var.mk 13

def klkksp := lang.classicalGeometry.expr.lit (classicalGeometry.mk 14 3)
def klkk := cmd.classicalGeometryAssmt (klkkvar) (klkksp)


def sakaskavar : lang.classicalGeometry.var := lang.classicalGeometry.var.mk 15

def sakaskasp := lang.classicalGeometry.expr.lit (classicalGeometry.mk 16 1)
def sakaska := cmd.classicalGeometryAssmt (sakaskavar) (sakaskasp)


def klklkvar : lang.classicalTime.var := lang.classicalTime.var.mk 17

def klklksp := lang.classicalTime.expr.lit (classicalTime.mk 18)
def klklk := cmd.classicalTimeAssmt (klklkvar) (klklksp)


def jjjjjjvar : lang.classicalVelocity.var := lang.classicalVelocity.var.mk 19

def jjjjjjsp := lang.classicalVelocity.expr.lit (classicalVelocity.mk 20)
def jjjjjj := cmd.classicalVelocityAssmt (jjjjjjvar) (jjjjjjsp)


def INDEX1633899366.STMTCOMMAND.B.L97C32.E.L110C1 : cmd :=(cmd.seq jjjjjj (cmd.seq klklk (cmd.seq sakaska klkk)))

