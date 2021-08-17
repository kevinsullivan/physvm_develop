import .physlib2

def length : PhysDimension := PhysDimension.mk 1 0 0
def mass : PhysDimension := PhysDimension.mk 0 1 0
-- following names already defined in physlib2 
def tyme : PhysDimension := PhysDimension.mk 0 0 1
def velosity : PhysDimension := PhysDimension.mk 1 0 (-1)

def MetersKilogramsSeconds : MeasurementSystem :=
    MeasurementSystem.mk lengthUnit.meter massUnit.kilogram timeUnit.second 

def twoMeters_in_MetersKilogramsSeconds : 
    PhysQuantity 
        length
        lengthUnit.meter
        massUnit.kilogram
        timeUnit.second := 
    PhysQuantity.mk 2 0 0

def twoMeters_in_CentimetersKilogramsSeconds : 
    PhysQuantity 
        length 
        lengthUnit.centimeter
        massUnit.kilogram
        timeUnit.second := 
    PhysQuantity.mk 200 0 0

def threeMeters_in_MetersKilogramsSeconds : 
    PhysQuantity 
        length 
        lengthUnit.meter
        massUnit.kilogram
        timeUnit.second := 
    PhysQuantity.mk 3 0 0

-- Should work
def fiveMeters := 
    physQuantityAdd
        twoMeters_in_MetersKilogramsSeconds
        threeMeters_in_MetersKilogramsSeconds

-- should not work
def fiveMeters' := 
    physQuantityAdd
        twoMeters_in_CentimetersKilogramsSeconds
        threeMeters_in_MetersKilogramsSeconds
