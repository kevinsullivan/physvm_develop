/-
This file will implement dimenion-indexed affine physical spaces.
It imports aff1Kcoord and exports aff1Kphys (d : dimension). It
works by extending space

The client is responsible for indexing dimensions. For convenience
we provide indexing by the usual LTM&t dimensions.
-/

def TIME := 0
def LENGTH := 1
def MASS := 3