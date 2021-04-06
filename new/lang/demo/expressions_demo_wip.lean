import ..expressions.time_expr_wip

--set up math and phys literals 
--assume the default interpretation is in seconds for now (in lieu of measurement system)
def world_time := time_std_space ℚ
def world_time_std := time_std_frame ℚ

--using frame as measurement unit as discussed
#check mk_space
def year_fm := mk_frame (mk_point world_time 0) (mk_vectr world_time (60*60*24*365))
def year_space := mk_space ℚ year_fm

--lang test

open lang.time

/-
Tests out various constructors of time and duration_expression.

Here, spc is only referenced in the construction of literal expressions.
-/


def now : time_expr := time_expr.lit ( mk_time year_space 0 ) 

def one_year : duration_expr := duration_expr.lit (mk_duration year_space 1)


def two_years : duration_expr := 2•one_year

def two_plus_one_years : duration_expr := one_year +ᵥ  two_years

def three_years_in_future : time_expr := two_plus_one_years +ᵥ now


def zero_years : duration_expr := duration_expr.zero
def still_zero_years := duration_expr.smul_dur (10000000:ℕ) zero_years

def zero_years_as_time_sub := now -ᵥ now +ᵥ zero_years +ᵥ still_zero_years


def duration_standard : duration_expr := duration_expr.lit (mk_duration world_time 1)

--Does not type check adding together durations in different spaces/frames
def invalid_expression_different_spaces : duration_expr := duration_standard +ᵥ one_year

def myenv := env.init
#check myenv
def myeval := eval.init

--You still need the expected space to get the result
--Unfortunately this type checks
def does_not_enforce_type_check := 
  let year_env := myenv.d year_space in
  let year_eval := myeval.d year_space in
  year_eval year_env invalid_expression_different_spaces

#eval does_not_enforce_type_check


def should_type_check : time year_space := 
  let year_env := myenv.t year_space in
  let year_eval := myeval.t year_space in
  year_eval year_env three_years_in_future

#eval pt_coord ℚ should_type_check.1.1 --well, eval not implemented yet

def tr_from_seconds_to_years := transform_expr.lit (world_time.time_tr year_space)

def tr_from_years_to_seconds := transform_expr.lit (year_space.time_tr world_time)

def tr_from_Seconds_to_seconds := transform_expr.compose tr_from_seconds_to_years tr_from_years_to_seconds

def invalid_composition := transform_expr.compose tr_from_seconds_to_years tr_from_seconds_to_years