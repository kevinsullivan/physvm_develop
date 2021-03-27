import data.real.basic
import .geom

/-
Comments in rest of file are out of date, written for time not geom. But same reasoning applies.
-/

open geom

abbreviation K := ℝ   -- or try ℚ for a computable version (but no square roots)

-- assume unit vector is one second in standard time space
noncomputable def t1 : position (std_space K) := mk_position (std_space K) 1          -- t=0 + 1 second
noncomputable def t2 := mk_position (std_space K) 3                               -- t=0 + 3 seconds
noncomputable def d1 : translation (std_space K) := t2 -ᵥ t1                     -- 2 seconds
noncomputable def t3 := 5 • d1 +ᵥ t1                                          -- t=0 + 11 seconds

-- new frame with origin at t=0 + 1hr and unit duration of 1 minute
noncomputable def t1' : position (std_space K) := mk_position (std_space K) 3600      -- t=0 + 1hr
noncomputable def d1' := 60 • (mk_duration (std_space K) 1)                                             -- one minute
noncomputable def new_fm := mk_frame t1'.to_point d1'.to_vectr                -- TODO: fix
noncomputable def new_space := mk_space K new_fm

-- create some points and vectors in new space
noncomputable def t1'' : position new_space := mk_position new_space 1                -- t=0 + 1 second (3660)
noncomputable def t2'' := mk_position new_space 3                                 -- t=0 + 3 seconds (3600 + 180)
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

-- #1: support end-to-end in Peirce (schedule discussion for lang-level design)
-- #2: get transforms working in this design (design proposal needed)
-- #3: re-imagine a tf-like API based on work in this style

-- fill in the proofs (low risk, low priority; postpone)
-- add helper functions to access coordinate values
-- get affine combinations working (not high priority)
-- fix that one problem where I break an abstraction boundry for lack of an at-level mk function
