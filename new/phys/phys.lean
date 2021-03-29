/-
This file will implement dimenion-indexed affine physical spaces.
It imports aff1Kcoord and exports aff1Kphys (d : dimension). It
works by extending space

The client is responsible for indexing dimensions. For convenience
we provide indexing by the usual LTM&t dimensions.
-/

import .time.time
import data.real.basic 

universes u
variables 
(K : Type u) [field K] [inhabited K] 

#check @time_std_frame ℝ 


#check @mk_time

def t0 := mk_time K