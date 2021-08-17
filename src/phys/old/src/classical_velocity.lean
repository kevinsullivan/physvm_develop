import .classical_geometry
import .classical_time

-- name serves as unique ID for a given geometric space
structure classicalVelocity : Type :=
mk :: (id : ℕ) (g : classicalGeometry) (t : classicalTime) 

-- provide standard 3D velocity object
def worldVelocity := classicalVelocity.mk 0 worldGeometry worldTime

-- TODO: Connect algebra of g to the algebra that is returned? Or is it already?
noncomputable def classicalVelocityAlgebra : classicalVelocity → Algebra
| (classicalVelocity.mk n g t) := Algebra.vector_space (to_vector 1)