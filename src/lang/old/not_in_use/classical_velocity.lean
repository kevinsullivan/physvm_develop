import ...phys.src.classical_velocity
import .classical_geometry
import .classical_time

namespace lang.classicalVelocity

structure var : Type :=
mk :: (num : ℕ)

def varEq : var → var → bool
| v1 v2 := v1.num=v2.num

def env := (var → classicalVelocity)

inductive expr : Type
| lit (v : classicalVelocity)
| var (v : var)
| div (g : lang.classicalGeometry.expr) (t : lang.classicalTime.expr)

def init := λ v : var, worldVelocity

end lang.classicalVelocity
