import ..expressions.time_expr_current

open lang.time

abbreviation F := lang.time.K 
lemma k_eq_Q : F = ℚ := rfl --lang is configured for the rationals

def world_time_in_seconds_fr : time_frame_expr := [time_std_frame F] 
def world_time_in_seconds : time_space_expr world_time_in_seconds_fr :=  
  [time_std_space F]

def world_time_in_years_fr : time_frame_expr := 
  let origin := [(mk_time world_time_in_seconds.value 0)] in
  let basis := [(mk_duration world_time_in_seconds.value (60*60*24*365))] in
  mk_time_frame_expr origin basis --not deeply embedded,
def world_time_in_years : time_space_expr world_time_in_years_fr :=
  mk_time_space_expr world_time_in_years_fr



def launch_time_in_seconds : time_expr world_time_in_seconds := 
  [(mk_time world_time_in_seconds.value 0)]

def launch_time_in_years : time_expr world_time_in_years :=
  [(mk_time world_time_in_years.value 0)]

def one_second : duration_expr world_time_in_seconds :=
  [(mk_duration world_time_in_seconds.value 1)]
def one_year : duration_expr world_time_in_years := 
  [(mk_duration world_time_in_years.value 1)]

--def adding_launches : time_expr world_time_in_seconds :=
--  launch_time_in_seconds +ᵥ launch_time_in_seconds --can't add times

def two_seconds : duration_expr world_time_in_seconds := 
  one_second +ᵥ one_second

def one_second_after_launch : time_expr world_time_in_seconds :=
  one_second +ᵥ launch_time_in_seconds

def what_after_what : _ :=
  one_second +ᵥ launch_time_in_years --wrong units

def two_years : duration_expr world_time_in_years :=
  one_second +ᵥ one_second

--def five_seconds : duration_expr world_time_in_seconds :=
--  5•one_second