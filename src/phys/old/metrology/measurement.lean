import .dimensions
import .unit

namespace measurementSystem

/-
We define a measurement system to be a 7-tuple
of units: one for length, one for mass, etc.
-/
structure MeasurementSystem : Type :=
mk ::
(length : unit.length)
(mass : unit.mass)
(time : unit.time)
(current : unit.current)
(temperature : unit.temperature)
(quantity : unit.quantity)
(intensity : unit.intensity) 

-- Examples

def si_measurement_system : MeasurementSystem :=
MeasurementSystem.mk 
unit.length.meter
unit.mass.kilogram
unit.time.second
unit.current.ampere
unit.temperature.kelvin
unit.quantity.mole
unit.intensity.candela

-- double check this and fix if necessary
def imperial_measurement_system : MeasurementSystem :=
MeasurementSystem.mk 
unit.length.foot
unit.mass.pound
unit.time.second
unit.current.ampere
unit.temperature.fahrenheit
unit.quantity.mole
unit.intensity.candela


end measurementSystem