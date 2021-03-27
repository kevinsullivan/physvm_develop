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

abbreviation K := ℝ   -- or try ℚ for a computable version (but no square roots)

-- assume unit vector is one second in standard time space
noncomputable def t1 : time (std_space K) := mk_time (std_space K) 1          -- t=0 + 1 second
noncomputable def t2 := mk_time (std_space K) 3                               -- t=0 + 3 seconds
noncomputable def d1 : duration (std_space K) := t2 -ᵥ t1                     -- 2 seconds
noncomputable def t3 := 5 • d1 +ᵥ t1                                          -- t=0 + 11 seconds

-- new frame with origin at t=0 + 1hr and unit duration of 1 minute
noncomputable def t1' : time (std_space K) := mk_time (std_space K) 3600      -- t=0 + 1hr
noncomputable def d1' := 60 • (mk_duration (std_space K) 1)                                             -- one minute
noncomputable def new_fm := mk_frame t1'.to_point d1'.to_vectr                -- TODO: fix
noncomputable def new_space := mk_space K new_fm

-- create some points and vectors in new space
noncomputable def t1'' : time new_space := mk_time new_space 1                -- t=0 + 1 second (3660)
noncomputable def t2'' := mk_time new_space 3                                 -- t=0 + 3 seconds (3600 + 180)
noncomputable def d1'' := t2'' -ᵥ t1''                                        -- 2 seconds
noncomputable def t3'' := 5 • d1'' +ᵥ t1''                                    -- 11 in the new space, what old?

-- check for type errors across difference coordinate systems on time
noncomputable def d_good := t1' -ᵥ t1     -- time - time = duration
noncomputable def t_good := 8 • d1' +ᵥ t1   -- scalar * duration + time = time
noncomputable def d_bad := t1'' -ᵥ t1     -- error: type mismatch in aff coord spaces
noncomputable def t_bad := 8 • d1'' +ᵥ t1 -- error: no impl of +ᵥ across aff coord spaces

/-
Afterthoughts
-/

-- fill in the proofs (low risk, low priority; postpone)
-- get transforms working in this design (design proposal needed)
-- support end-to-end in Peirce (schedule discussion for lang-level design)

-- add helper functions to access coordinates directly
-- get affine combinations working (not high priority)
-- re-imagine a tf-like API based on work in this style
