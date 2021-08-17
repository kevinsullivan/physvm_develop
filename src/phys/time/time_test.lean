import data.real.basic
import .time

/-
Outstanding problems: 
  - render C++ physics to clean physically type-checked expressions in Lean
  - need MVP for "time" as an affine space with arbitrary affine coordinate space overlays
    - need general library supporting (1-D) affine space API, used to implement physical time  
    - need version of Peirce working end-to-end with terms having physical type, time
Progress this week:
  - assessed situation with respect to affine space and time library
  - decided to use what I've learned from working with students to "get it done"
  - goal: clearly implement an "affine algebra of time" as a semantic domain for Peirce
  - approach: 
      - MVP: pick a 1-D problem
      - *Build from the mathematics up* rather than from some front-end preconception down
      - Represent 1-D affine space as 2-D linear space in the usual way
      - Instantiate vector_space typeclass for 2-D linear space (operations and notations)
      - Build 1-D bare (no frames) affine space algebra, instantiating affine_space typeclass
      - Each layer of the design is *cleanly* implemented in terms of immediately preceding layer
      - Build up from here by *extending* low-level abstractions, instantiating affine_space each time
        - vc (linear 2-D K space)
        - pt, vec, fm (affine 1-D K space)
        - point, vectr, frame, coordinate space
        - time, duration, frame, coordinate space
      - provide examples/tests to show the algebra at each level
    - contribution: enable progress in this project
    - next steps: discuss after presentation
-/

--abbreviation K :=ℚ   -- or try ℚ for a computable version (but no square roots)

-- assume unit vector is one second in standard time space
#check time_std_space


 def t1 : time (time_std_space) :=  mk_time (time_std_space)  1          -- t=0 + 1 second
 def t2 := mk_time (time_std_space) 3                             -- t=0 + 3 seconds
 def d1 : duration (time_std_space) := t2 -ᵥ t1                     -- 2 seconds
 def t3 := 5 • d1 +ᵥ t1                                          -- t=0 + 11 seconds

-- new frame with origin at t=0 + 1hr and unit duration of 1 minute
 def t1' := mk_time (time_std_space) 3600      -- t=0 + 1hr

#eval t1'.coords

 def d1' := 60 • (mk_duration (time_std_space) 1)                                             -- one minute
 def new_fm := mk_frame t1'.to_point d1'.to_vectr                -- TODO: fix
 def new_space := mk_space scalar new_fm

-- create some points and vectors in new space
 def t1'' : time new_space := mk_time new_space 1                -- t=0 + 1 second (3660)
 def t2'' := mk_time new_space 3                                 -- t=0 + 3 seconds (3600 + 180)

def t3'' := mk_duration new_space 5

def mytr := (time_std_space).mk_time_transform_to new_space

#check mytr

def ftr := (new_space).time_tr (time_std_space K)

#check ftr
#eval (mytr.transform_time t1).to_point.to_pt.to_prod




/-
Afterthoughts
-/

-- fill in the proofs (low risk, low priority; postpone)
-- get transforms working in this design (design proposal needed)
-- support end-to-end in Peirce (schedule discussion for lang-level design)

-- add helper functions to access coordinates directly
-- get affine combinations working (not high priority)
-- re-imagine a tf-like API based on work in this style
