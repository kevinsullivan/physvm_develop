import ..phys.time.time

/-
Units are in seconds. Seconds are the smallest non-variable unit in UTC.
-/

noncomputable def coordinated_universal_time_in_seconds : time_space _ := 
  let origin := mk_time time_std_space (1970*365*24*60*60) in
  let basis := mk_duration time_std_space 1 in 
  mk_space (mk_time_frame origin basis)