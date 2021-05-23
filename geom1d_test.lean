import .lang.expressions.time_expr
import .lang.expressions.geom1d_expr

open lang.time
open lang.geom1d
def meters_fr : geom1d_frame_expr := |geom1d_std_frame|
def meters : geom1d_space_expr meters_fr := |geom1d_std_space|

def kilometers_fr : geom1d_frame_expr := 
 let origin := |mk_position meters.value 0.000000| in
 let basis := |mk_displacement meters.value 1000.000000| in
 mk_geom1d_frame_expr origin basis
def kilometers : geom1d_space_expr kilometers_fr := mk_geom1d_space_expr kilometers_fr

def launch_time_in_seconds : _ := |mk_position meters.value 1.000000|
def launch_time_in_years : _ := |mk_position kilometers.value 1.000000|
def one_second : _ := |mk_displacement meters.value 1.000000|
def one_year : _ := |mk_displacement kilometers.value 1.000000|
def two_seconds : _ := one_second+ᵥone_second
def one_second_after_launch : _ := launch_time_in_seconds+ᵥone_second
def what_after_what : _ := launch_time_in_years+ᵥone_second
def two_years : _ := one_second+ᵥone_second
def seconds_to_years : _ := |meters.value.mk_geom1d_transform_to kilometers.value|
def five_seconds : _ := |mk_displacement meters.value 5.000000|
def five_secs_in_years : _ := seconds_to_years⬝five_seconds.value
