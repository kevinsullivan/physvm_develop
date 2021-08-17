import .classical_velocity
import .classical_time

-- id serves as unique ID for a given acceleration space
structure classicalAcceleration : Type :=
mk :: (id : ℕ) (v : classicalVelocity) (t : classicalTime) 

-- provide standard 3D acceleration object
def worldAcceleration := classicalAcceleration.mk 0 worldVelocity worldTime

--returns vector space of the same dimension as the built in geometric space
noncomputable def classicalAccelerationAlgebra : classicalAcceleration → Algebra
| (classicalAcceleration.mk n v t) := Algebra.vector_space (to_vector v.g.dim)