import ..metrology.dimension

open dimension
/-
Here we give standard physics names to a few derived dimensions. This
list can be greatly extended. This should move to phys.
-/

-- Names for basic dimensions as dimensions
def length := basicDimToDim BasicDimension.length 
def mass := basicDimToDim BasicDimension.mass 
def time := basicDimToDim BasicDimension.time
def current := basicDimToDim BasicDimension.current
def temperature := basicDimToDim BasicDimension.temperature
def quantity := basicDimToDim BasicDimension.quantity
def intensity := basicDimToDim BasicDimension.intensity

-- And now some deried dimension
def area := mul length length
def volume := mul area length
def velocity := div length time
def acceleration := div velocity time
def density := div quantity volume
-- etc

