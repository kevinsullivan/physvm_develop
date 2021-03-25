import .affine1K_standard
import data.real.basic
import .time

-- assume unit vector is one second in standard time space
noncomputable def t1 : time (std_space ℝ) := mk_time (std_space ℝ) (1:ℝ)    -- t=0 + 1 second
noncomputable def t2 := mk_time (std_space ℝ) (3:ℝ)                         -- t=0 + 3 seconds
noncomputable def d1 : duration (std_space ℝ) := t2 -ᵥ t1                     -- 2 seconds
noncomputable def t3 := 5 • d1 +ᵥ t1                                          -- t=0 + 10 seconds

-- new frame with origin at t=0 + 1hr and unit duration of 1 minute
noncomputable def t1' : time (std_space ℝ) := mk_time (std_space ℝ) (3600:ℝ)  -- t=0 + 1hr
noncomputable def d1' := 60 • d1                                              -- one minute
noncomputable def new_fm := mk_frame t1'.to_point d1'.to_vectr
noncomputable def new_space := mk_space ℝ new_fm

-- create some points and vectors in new space
noncomputable def t1'' : time new_space := mk_time new_space (1:ℝ)            -- t=0 + 1 second
noncomputable def t2'' := mk_time new_space (3:ℝ)                             -- t=0 + 3 seconds
noncomputable def d1'' := t2'' -ᵥ t1''                                        -- 2 seconds
noncomputable def t3'' := 5 • d1'' +ᵥ t1''

-- check for type errors across difference coordinate systems on time
noncomputable def d_good := t1' -ᵥ t1
noncomputable def t_good := d1' +ᵥ t1
noncomputable def d_bad := t1'' -ᵥ t1
noncomputable def t_bad := d1'' +ᵥ t1
