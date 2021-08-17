import .quantity

open quantity
open dimension
open measurementSystem

-- Examples

def oneMeter := mkQuantity BasicDimension.length si_measurement_system (1 : ℝ)
def twoSeconds := mkQuantity BasicDimension.time si_measurement_system (2 : ℝ)
def threePounds := mkQuantity BasicDimension.mass imperial_measurement_system ⟨(3 : ℝ), by linarith ⟩

/-
Kevin: Note that at this point we can only make quantities from basic dimensions,
so if we want a derived quantity, we have to derive it from quantities made in this
way.
-/


#check threePounds

