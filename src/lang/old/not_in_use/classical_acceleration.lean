import ...phys.src.classical_acceleration
import .classical_velocity
import .classical_time

namespace lang.classicalAcceleration

structure var : Type :=
mk :: (num : ℕ)

def varEq : var → var → bool
| v1 v2 := v1.num=v2.num

def env := (var → classicalAcceleration)

inductive expr : Type
| lit (v : classicalAcceleration)
| var (v : var)
| div (v : lang.classicalVelocity.expr) (t : lang.classicalTime.expr)

def init := λ v : var, worldAcceleration

end lang.classicalAcceleration