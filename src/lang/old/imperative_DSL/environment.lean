import ..expressions.classical_geometry
import ..expressions.classical_time
import ..expressions.classical_hertz
import ..expressions.classical_luminous_intensity
--import ..expressions.classical_velocity
import ..expressions.boolean
import ..expressions.measurementSystem
import ..expressions.axis_orientation
--import ..expressions.classical_acceleration

noncomputable theory

namespace environment
structure env : Type :=
mk ::   --(g: lang.classicalGeometry.spaceEnv)
        (t: lang.classicalTime.env)
        (g: lang.euclideanGeometry3.env)
        (h: lang.classicalHertz.env)
        (li: lang.classicalLuminousIntensity.env)
        (ms: lang.measurementSystem.env)
        (ax : lang.axisOrientation.env)
        --(v: lang.classicalVelocity.env)
        --(a: lang.classicalAcceleration.env)

def init_env :env := --env.mk 
--                    lang.classicalGeometry.init
                   ⟨
                   lang.classicalTime.initEnv, 
                   lang.euclideanGeometry3.initEnv, 
                   lang.classicalHertz.initEnv,
                   lang.classicalLuminousIntensity.initEnv,
                   lang.measurementSystem.initEnv,
                   lang.axisOrientation.initEnv
                   ⟩
--                    lang.classicalVelocity.init
--                    lang.classicalAcceleration.init
end environment