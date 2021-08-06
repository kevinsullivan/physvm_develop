import .lang.lang
open lang.time
open lang.geom1d
open lang.geom3d
open lang.series.geom3d
open lang.bool_expr
namespace peirce_output
noncomputable theory

def wt_fr : time_frame_expr := |time_std_frame|
def wt : time_space_expr wt_fr := |time_std_space|

def ww_fr : geom3d_frame_expr := |geom3d_std_frame|
def ww : geom3d_space_expr ww_fr := |geom3d_std_space|


def func_test : displacement3d_expr ww := 
  ((
  ((|mk_displacement3d ww.value 0.000000 0.000000 0.000000|:displacement3d_expr ww))
  :_))

def tst2 : displacement3d_expr ww := 
  ((
  let vecvec : displacement3d_expr ww := ((|mk_displacement3d ww.value 0.000000 0.000000 0.000000|:displacement3d_expr ww)) in
  ((vecvec:displacement3d_expr ww))
  :_))

def arg_test : displacement3d_expr ww → time_expr wt → duration_expr wt := 
  λ arg, λ tmmmm, ((
  let dur : duration_expr wt := ((|mk_duration wt.value 5.000000|:duration_expr wt)) in
  let dur2 : duration_expr wt := ((((|mk_duration wt.value 5.000000|:duration_expr wt))+ᵥ((dur : duration_expr wt)):duration_expr wt)) in
  ((dur2 : duration_expr wt))
  :_))

def noop : displacement3d_expr ww → time_expr wt → punit := 
λ vv, λ tm, 
  punit.star

def main : punit := 
  let arg : displacement3d_expr ww := ((|mk_displacement3d ww.value 0.000000 0.000000 0.000000|:displacement3d_expr ww)) in
  let res : displacement3d_expr ww := func_test in
  let now : displacement3d_expr ww := ((|mk_displacement3d ww.value 0.000000 0.000000 0.000000|:displacement3d_expr ww)) in
  let res3 : duration_expr wt := arg_test ((|mk_displacement3d ww.value 0.000000 0.000000 0.000000|:displacement3d_expr ww)) ((|mk_time wt.value 0.000000|:time_expr wt)) in

  punit.star



end peirce_output