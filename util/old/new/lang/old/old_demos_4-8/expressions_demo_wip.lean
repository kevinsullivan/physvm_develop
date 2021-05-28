import ..expressions.time_expr_wip

open lang.time

def env_ := env.init
def eval_ := eval.init

--set up math and phys literals 
--assume the default interpretation is in seconds for now (in lieu of measurement system)
def world_time : time_space_expr := [(time_std_space ℚ)]
def world_time_std := [(time_std_frame ℚ)]

--using frame as measurement unit as discussed
#check mk_space

def year_origin : time_expr := 
  let frame_lit := (eval_.frame_eval env_.frame_env world_time_std) in
  let std_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) world_time) in
  [(mk_time std_lit 0)]

def year_basis : duration_expr := 
  let frame_lit := (eval_.frame_eval env_.frame_env world_time_std) in
  let std_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) world_time) in
  [(mk_duration std_lit 0)]

def year_fm := mk_time_frame_expr year_origin year_basis
def year_space := 
  let frame_lit := (eval_.frame_eval env_.frame_env world_time_std) in
  let std_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) world_time) in
  mk_time_space_expr ℚ year_fm

/-
Tests out various constructors of time and duration_expression.

Here, spc is only referenced in the construction of literal expressions.
-/


def now : time_expr := 
  let frame_lit := (eval_.frame_eval env_.frame_env year_fm) in
  let year_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) year_space) in
  [(mk_time year_lit 0)] 

def one_year : duration_expr := 
  let frame_lit := (eval_.frame_eval env_.frame_env year_fm) in
  let year_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) year_space) in
  [(mk_duration year_lit 1)]


def two_years : duration_expr := 2•one_year

def two_plus_one_years : duration_expr := one_year +ᵥ  two_years

def three_years_in_future : time_expr := two_plus_one_years +ᵥ now


def zero_years : duration_expr := duration_expr.zero
def still_zero_years := duration_expr.smul_dur (10000000:ℕ) zero_years

def zero_years_as_time_sub := now -ᵥ now +ᵥ zero_years +ᵥ still_zero_years


def duration_standard : duration_expr := 
  let frame_lit := (eval_.frame_eval env_.frame_env world_time_std) in
  let std_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) world_time) in
  [(mk_duration std_lit 1)]

--Does not type check adding together durations in different spaces/frames
def invalid_expression_different_spaces : duration_expr := duration_standard +ᵥ one_year


--You still need the expected space to get the result
--Unfortunately this type checks 
--Updated comment 4/6 - unfortunately "current" version 
--with more explicit typing is susceptible to very similar weak typing errors as well
--Thus, while it's a problem, it's not exclusive to this version of lang
def does_not_enforce_type_check := 
  let frame_lit := (eval_.frame_eval env_.frame_env year_fm) in
  let year_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) year_space) in
  let year_env := env_.duration_env year_lit in
  let year_eval := eval_.duration_eval year_lit in
  year_eval year_env invalid_expression_different_spaces

#eval does_not_enforce_type_check


def should_type_check : 
  let frame_lit := (eval_.frame_eval env_.frame_env year_fm) in
  let year_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) year_space) in
  time year_lit := 
  let frame_lit := (eval_.frame_eval env_.frame_env year_fm) in
  let year_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) year_space) in
  let year_env := env_.time_env year_lit in
  let year_eval := eval_.time_eval year_lit in
  year_eval year_env three_years_in_future

#eval pt_coord ℚ should_type_check.1.1 --well, eval not implemented yet

def tr_from_seconds_to_years := 
  let year_frame_lit := (eval_.frame_eval env_.frame_env year_fm) in
  let year_lit := ((eval_.space_eval year_frame_lit) (env_.space_env year_frame_lit) year_space) in
  let frame_lit := (eval_.frame_eval env_.frame_env world_time_std) in
  let std_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) world_time) in
  
  transform_expr.lit (std_lit.time_tr year_lit)

def tr_from_years_to_seconds := 
  let year_frame_lit := (eval_.frame_eval env_.frame_env year_fm) in
  let year_lit := ((eval_.space_eval year_frame_lit) (env_.space_env year_frame_lit) year_space) in
  let frame_lit := (eval_.frame_eval env_.frame_env world_time_std) in
  let std_lit := ((eval_.space_eval frame_lit) (env_.space_env frame_lit) world_time) in
  transform_expr.lit (year_lit.time_tr std_lit)

def tr_from_Seconds_to_seconds := transform_expr.compose tr_from_seconds_to_years tr_from_years_to_seconds

def invalid_composition := transform_expr.compose tr_from_seconds_to_years tr_from_seconds_to_years