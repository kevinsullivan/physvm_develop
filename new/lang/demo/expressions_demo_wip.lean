import ..expressions.time_expr_wip

--set up math and phys literals to 

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
def two_years : duration_expr := duration_expr.smul_dur (2 : ℚ) one_year

def two_plus_one_years : duration_expr := duration_expr.add_dur_dur one_year two_years

def three_years_in_future : time_expr := time_expr.add_dur_time two_plus_one_years now


def zero_years := duration_expr.zero ℚ
def still_zero_years := duration_expr.smul_dur (10000000:ℚ) zero_years

def zero_years_as_time_sub := duration_expr.sub_time_time now now