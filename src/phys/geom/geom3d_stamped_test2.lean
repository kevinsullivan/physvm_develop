import .geom3d_series
import tactic.linarith

def ts := time_std_space

def world_fr := geom3d_std_frame
def world := geom3d_std_space

def bl_fr := 
 let origin := mk_position3d world 1.000000 2.000000 3.000000 in
 let basis0 := mk_displacement3d world 4.000000 3.000000 2.000000 in
 let basis1 := mk_displacement3d world 1.000000 2.000000 3.000000 in
 let basis2 := mk_displacement3d world 2.000000 1.000000 2.000000 in
 mk_geom3d_frame origin basis0 basis1 basis2

def fr1 := 
 let origin := mk_position3d world 2.000000 4.000000 3.000000 in
 let basis0 := mk_displacement3d world 4.000000 3.000000 2.000000 in
 let basis1 := mk_displacement3d world 1.000000 2.000000 3.000000 in
 let basis2 := mk_displacement3d world 2.000000 1.000000 2.000000 in
 mk_geom3d_frame origin basis0 basis1 basis2

def fr2 := 
 let origin := mk_position3d world 4.000000 4.000000 3.000000 in
 let basis0 := mk_displacement3d world 4.000000 3.000000 2.000000 in
 let basis1 := mk_displacement3d world 1.000000 2.000000 3.000000 in
 let basis2 := mk_displacement3d world 2.000000 1.000000 2.000000 in
 mk_geom3d_frame origin basis0 basis1 basis2

def ser : geom3d_series ts := 
  ⟨
    [
      (mk_time _ 2,world_fr)--,
    --  (mk_time _ 1,fr1),
      --(mk_time _ 0,fr2)
  
      --(mk_time _ 2),
      --(mk_time _ 1),
      --(mk_time _ 0)
    ]⟩
/-(⟨mk_time _ 0,sorry⟩-/

#eval ser

#check quotient.eq

def v1 := mk_displacement3d_timefixed_at_time ser (mk_time ts (2.4:ℚ)) 1 1 1

def v2 := mk_displacement3d_timefixed_at_time ser (mk_time ts (2.5:ℚ)) 1 1 1

example : v1.frame = world_fr := begin
  unfold displacement3d.frame,
  unfold geom3d_series.find,
  split,
end

example : v1.frame = v2.frame := begin
  dsimp [displacement3d.frame],
  split,
end

#check v1 +ᵥ v2

def t1 := ⟦(⟨(mk_time ts (2.4:ℚ))⟩ : series_index ts ser)⟧
def t2 := ⟦(⟨(mk_time ts (2.5:ℚ))⟩ : series_index ts ser)⟧

example : t1 = t2 := sorry

#check t1

#check quotient.lift

def v3 := mk_displacement3d_timefixed_at_time'' ser ⟦series_index.mk (mk_time ts (2.4:ℚ))⟧ 1 1 1

def v4 := mk_displacement3d_timefixed_at_time'' ser ⟦series_index.mk (mk_time ts (2.5:ℚ))⟧ 1 1 1

#check v3 +ᵥ v4