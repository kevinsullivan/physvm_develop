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
      --(mk_time _ 0,world_fr),
      --(mk_time _ 1,fr1),
      --(mk_time _ 2,fr2)
  
      (mk_time _ 2),
      (mk_time _ 1),
      (mk_time _ 0)
    ]⟩
/-(⟨mk_time _ 0,sorry⟩-/

#eval ser

def v1 := mk_displacement3d_timefixed_at_time ser (mk_time ts (0.4:ℚ)) 1 1 1
#check v1

def v2 := mk_displacement3d_timefixed_at_time ser (mk_time ts (0.5:ℚ)) 1 1 1
#check v2

#check v1 +ᵥ v2
def s1 : series_index ts ser := ⟨mk_time ts (0.5:ℚ)⟩
def s2 : series_index ts ser := ⟨mk_time ts (2.5:ℚ)⟩
#eval s1.idx.coord
#eval s2.idx.coord
#eval (ser.find_index s1.idx).coord
#eval (ser.find_index s2.idx).coord
#check quot.lift
#check has_equiv
/-
attribute [reducible, elab_as_eliminator]
protected def lift {α : Sort u} {β : Sort v} [s : setoid α] (f : α → β) : (∀ a b, a ≈ b → f a = f b) → quotient s → β :=
quot.lift f
-/
def lift_si : series_index ts ser → time ts :=
  λsi, (ser.find_index si.idx)

def lift_ := quotient.lift lift_si begin 
  dsimp [has_equiv.equiv],
  unfold lift_si,
  unfold setoid.r,
  unfold index_rel,
  intros a b c,
  exact c,
end

def chk := index_rel ts s1 s2
#eval chk

#eval ⟦s1⟧=⟦s2⟧
#eval (lift_ ⟦s1⟧).coord
#eval (lift_ ⟦s2⟧).coord
#eval (lift_ ⟦s1⟧)
#eval (lift_ ⟦s2⟧)

def pt111 : (lift_ ⟦s1⟧).coord = (lift_ ⟦s2⟧).coord := begin
  simp *,
end

def pttt : (lift_ ⟦s1⟧).coord = (lift_ ⟦s2⟧).coord := begin
  unfold lift_,
end


def lift_2 : ℕ → ℚ :=
  λsi, si

instance : setoid ℕ := ⟨ 
  (λn1 n2, n1=n2), sorry
⟩

def lift2_ := quotient.lift lift_2 begin 
  --intros,
 -- unfold lift_2,
  dsimp [has_equiv.equiv],
  unfold setoid.r,
  unfold lift_2,
  simp *,
end

def ss11 := ⟦1⟧
def ss22 := ⟦1⟧

lemma a1 : ss11 = ss22 := rfl

lemma a2 :  lift2_ ss11 =  lift2_ ss22 := rfl
#eval lift2_ ss11

