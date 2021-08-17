import ..time.time
import tactic.ext

universes u

variables   {tf : time_frame} (ts : time_space tf) (V : Type u) 
  [inhabited V] /-Questionable whether to use inhabited.default as a default value-/
/-
structure timestamped :=
  (timestamp : time ts)

@[class]
structure has_timestamp (V : Type u) :=
  (get_timestamp : V → time ts)

instance : has_timestamp ts (timestamped ts) := ⟨λts, ts.timestamp⟩
-/
structure timestamped :=
(timestamp : time ts)
(value : V)

@[simp]
noncomputable def mk_default_timestamped : timestamped ts V := 
  ⟨inhabited.default (time ts), inhabited.default V⟩

noncomputable instance : inhabited (timestamped ts V) := ⟨mk_default_timestamped ts V⟩


@[simp]
lemma nathelper :  ∀ (a b : ℕ), a + b < a → false := 
begin
  intros a b c,
  cases b,
  suffices : ¬a < a, from by contradiction, exact irrefl _,
  let h1 : 0 < b.succ := by simp *,
  let h2 : a + 0 < a + b.succ := by simp *,
  let h3 : a + 0 < a := by exact lt_trans h2 c,
  suffices : ¬a < a, from by contradiction, exact irrefl _,

end


@[simp]
lemma nathelper2 :  ∀ (a b : ℕ), b + a < a → false := 
begin
  intros a b c,
  rw ←(nat.add_comm a b) at c,
  exact nathelper _ _ c,
end
/-

    let ht :  i_val + 1 = i_val.succ := by repeat { apply nat.add_one _ },
          rw ←ht at i_property,
          let : false := by exact eznat2 _ _ i_property,
    contradiction,
-/
instance timelt : has_lt (time ts) := ⟨
  λt1 t2, t1.coord < t2.coord
⟩
instance timele : has_le (time ts) := ⟨ 
  λt1 t2, t1.coord ≤ t2.coord
⟩

instance [has_le (time ts)] [has_lt (time ts)]: preorder (time ts) := ⟨ 
  --has_le.le, has_lt.lt, 
  λt1 t2, t1.coord ≤ t2.coord,
  λt1 t2, t1.coord < t2.coord,
  begin
    intros,
    simp *,
  end,
  begin
    simp *,
    intros a b c d e,
    transitivity,
    apply d,
    apply e,
    --simp
  end,
  begin
    simp *,
    intros a b,
    split,
    assume h,
    split,
    exact (le_not_le_of_lt h).1,
    apply h,
    assume h,
    exact h.2,
  end
⟩
noncomputable instance eqd {t1 t2 : time ts} : decidable (t1 = t2) := 
  if eqc:t1.coord=t2.coord then
    begin
      --cases t1, cases t2, cases t1, cases t2,
      unfold time.coord at eqc,
      cases t1,cases t2,
      let h : ∀i, t1.coords i = t2.coords i := begin
        intros,
        cases i,
        cases i_val,
        ext,
        exact eqc,
        let ht :  i_val + 1 = i_val.succ := by repeat { apply nat.add_one _ },rw ←ht at i_property,
        let : false := by exact nathelper2 _ _ i_property,
        contradiction,
      end,
      let h1 : t1 = t2 := begin ext, 
        let h := h x,
        simp [h],
      end,
      simp [h1],
      exact decidable.is_true true.intro,
    end
  else 
    begin
      --cases t1, cases t2, cases t1, cases t2,
      unfold time.coord at eqc,
      cases t1,cases t2,
      let h : ∀i, ¬t1.coords i = t2.coords i := begin
        intros,
        cases i,
        cases i_val,
        cases (t1.coords ⟨0, i_property⟩),
        cases (t2.coords ⟨0, i_property⟩),
        simp [eqc],

        --ext,
        let ht :  i_val + 1 = i_val.succ := by repeat { apply nat.add_one _ },rw ←ht at i_property,
        let : false := by exact nathelper2 _ _ i_property,
        contradiction,
      end,
      let h1 : ¬t1 = t2 := begin assume teq,
        let : (({to_point := t1} : time _).to_point.coords 0).coord = 
              (({to_point := t2} : time _).to_point.coords 0).coord :=
          by rw ←teq,
        contradiction
      end,
      --simp [h1],
      exact decidable.is_false (by simp [h1]),
    end

--instance ltd {t1 t2 : time ts} : decidable (t1 < t2) := sorry
--instance leqd {t1 t2 : time ts} : decidable (t1 ≤ t2) := sorry

abbreviation time_series := time ts → V

abbreviation time_series.Icc (min_t max_t : time ts) := 
  set.Icc min_t max_t → V 

abbreviation time_series.Ici (min_t : time ts) := 
  set.Ici min_t → V 

def time_series.mk_empty {tf : time_frame} {ts : time_space tf} {V : Type u} 
  [inhabited V] 
  : time_series ts V := λi, inhabited.default V 

noncomputable def time_series.update {tf : time_frame} {ts : time_space tf} {V : Type u} 
  [inhabited V] : 
  time_series ts V → time ts → V → time_series ts V 
| ser t_ val_ := --λt, if t = t_ then val_ else ser t
  function.update ser t_ val_

def time_series.sample {tf : time_frame} {ts : time_space tf} {V : Type u} 
  [inhabited V] 
  : time_series ts V → time ts → V := 
  λser tm , ser tm

def time_series.Icc.sample 
  {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] {min_t max_t : time ts}
  : time_series.Icc ts V min_t max_t → set.Icc min_t max_t → V := 
  λser tm , ser tm

def time_series.Ici.sample 
  {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] {min_t : time ts}
  : time_series.Ici ts V min_t → set.Ici min_t → V := 
  λser tm , ser tm

abbreviation discrete_series {tf : time_frame} (ts : time_space tf) (V : Type u) [inhabited V] :=
  list (timestamped ts V)

def discrete_series.mk_empty {tf : time_frame} {ts : time_space tf} {V : Type u} 
  [inhabited V] : discrete_series ts V := []

#check list.range
#check set.mem

def discrete_series.domain {tf : time_frame} {ts : time_space tf} {V : Type u} 
  [inhabited V] :
  discrete_series ts V → list (time ts) := 
  λser, list.map (λtsv : timestamped ts V, tsv.timestamp) ser

def discrete_series.update {tf : time_frame} {ts : time_space tf} {V : Type u} 
  [inhabited V] :
  discrete_series ts V → timestamped ts V → discrete_series ts V
--| [] ts_ val_ := [(ts_, val_)]
--| (h::t) ts_ val_ := (h::t ++ [(ts_, val_)] :  list (timestamped ts V))
| ser tsv := ser.cons tsv

@[simp, reducible]
noncomputable def discrete_series.latest_helper {tf : time_frame} {ts : time_space tf} {V : Type u}
  [inhabited V] :
  discrete_series ts V → (timestamped ts V) → (timestamped ts V)
| (h::t) v := if h.timestamp > v.timestamp then discrete_series.latest_helper t h else discrete_series.latest_helper t v
| [] v := v

@[simp, reducible]
noncomputable def discrete_series.latest {tf : time_frame} {ts : time_space tf} {V : Type u} 
  [inhabited V] :
  discrete_series ts V → (timestamped ts V)
| (h::t) := discrete_series.latest_helper t h
| [] :=  ⟨inhabited.default (time ts), inhabited.default V⟩

abbreviation discrete_series.Icc {tf : time_frame} (ts : time_space tf) (V : Type u) [inhabited V]
  (min_t max_t : time ts) :=
  list (set.Icc min_t max_t × V)

abbreviation discrete_series.Ici {tf : time_frame} (ts : time_space tf) (V : Type u) [inhabited V]
  (min_t : time ts) :=
  list (set.Ici min_t × V)

noncomputable def discrete_series.sample  {tf : time_frame} {ts : time_space tf} {V : Type u} 
  [inhabited V] 
  : discrete_series ts V → time ts → V
| [] t_ := inhabited.default V
| (h::t) t_ := if h.timestamp = t_ then h.value else discrete_series.sample t t_ 

noncomputable def discrete_series.sample_floor_helper {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] 
  (v : time ts) : discrete_series ts V → option (timestamped ts V) → V
| [] (none) := inhabited.default V
| [] (some t_) := t_.value
| (h::t) (some t_) := 
  if t_.timestamp < h.timestamp ∧ h.timestamp ≤ v 
  then discrete_series.sample_floor_helper t (some h) 
  else discrete_series.sample_floor_helper t (some t_)
| (h::t) (none) := 
  if h.timestamp ≤ v 
  then discrete_series.sample_floor_helper t (some h) 
  else discrete_series.sample_floor_helper t none

noncomputable def discrete_series.sample_floor {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] 
  : discrete_series ts V → time ts → V := 
  λser t, discrete_series.sample_floor_helper t ser none

noncomputable def discrete_series.sample_ceil_helper {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] 
  (v : time ts) : discrete_series ts V → option (timestamped ts V) → V
| [] (none) := inhabited.default V
| [] (some t_) := t_.value
| (h::t) (some t_) := 
  if h.timestamp < t_.timestamp ∧ v ≤ h.timestamp
  then discrete_series.sample_ceil_helper t (some h) 
  else discrete_series.sample_ceil_helper t (some t_)
| (h::t) (none) := 
  if v ≤ h.timestamp 
  then discrete_series.sample_ceil_helper t (some h) 
  else discrete_series.sample_ceil_helper t none


noncomputable def discrete_series.sample_ceil {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] 
  : discrete_series ts V → time ts → V := 
  λser t, discrete_series.sample_ceil_helper t ser none

noncomputable def discrete_series.Icc.sample {min_t max_t : time ts}
  : discrete_series.Icc ts V min_t max_t → time ts → V
| [] t_ := inhabited.default V
| (h::t) t_ := if h.timestamp.1 = t_ then h.value else discrete_series.Icc.sample t t_ 


noncomputable def discrete_series.Icc.sample_floor_helper {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] {min_t max_t : time ts}
  (v : set.Icc min_t max_t) : discrete_series.Icc ts V min_t max_t → option (set.Icc min_t max_t × V) → V
| [] (none) := inhabited.default V
| [] (some t_) := t_.value
| (h::t) (some t_) := 
  if t_.timestamp.val < h.timestamp ∧ h.timestamp.val ≤ v 
  then discrete_series.Icc.sample_floor_helper t (some h) 
  else discrete_series.Icc.sample_floor_helper t (some t_)
| (h::t) (none) := 
  if h.timestamp.val ≤ v 
  then discrete_series.Icc.sample_floor_helper t (some h) 
  else discrete_series.Icc.sample_floor_helper t none


def discrete_series.Icc.sample_floor 
  {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] {min_t max_t : time ts}
  : discrete_series.Icc ts V min_t max_t → set.Icc min_t max_t → V := 
  λser t, discrete_series.Icc.sample_floor_helper t ser none


def discrete_series.Icc.sample_ceil_helper {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] {min_t max_t : time ts}
  (v : set.Icc min_t max_t) : discrete_series.Icc ts V min_t max_t → option (set.Icc min_t max_t × V) → V
| [] (none) := inhabited.default V
| [] (some t_) := t_.value
| (h::t) (some t_) := 
  if h.timestamp.val < t_.timestamp.val ∧ v.val ≤ h.timestamp.val
  then discrete_series.Icc.sample_ceil_helper t (some h) 
  else discrete_series.Icc.sample_ceil_helper t (some t_)
| (h::t) (none) := 
  if v.val ≤ h.timestamp.val
  then discrete_series.Icc.sample_ceil_helper t (some h) 
  else discrete_series.Icc.sample_ceil_helper t none


def discrete_series.Icc.sample_ceil {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] {min_t max_t : time ts}
  : discrete_series.Icc ts V min_t max_t → set.Icc min_t max_t → V := 
  λser t, discrete_series.Icc.sample_ceil_helper t ser none


def discrete_series.Ici.sample {min_t : time ts}
  : discrete_series.Ici ts V min_t → time ts → V
| [] t_ := inhabited.default V
| (h::t) t_ := if h.timestamp.1 = t_ then h.value else discrete_series.Ici.sample t t_ 


def discrete_series.Ici.sample_floor_helper {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] {min_t : time ts}
  (v : set.Ici min_t) : discrete_series.Ici ts V min_t → option (set.Ici min_t × V) → V
| [] (none) := inhabited.default V
| [] (some t_) := t_.value
| (h::t) (some t_) := 
  if t_.timestamp.val < h.timestamp ∧ h.timestamp.val ≤ v 
  then discrete_series.Ici.sample_floor_helper t (some h) 
  else discrete_series.Ici.sample_floor_helper t (some t_)
| (h::t) (none) := 
  if h.timestamp.val ≤ v 
  then discrete_series.Ici.sample_floor_helper t (some h) 
  else discrete_series.Ici.sample_floor_helper t none


def discrete_series.Ici.sample_floor 
  {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] {min_t : time ts}
  : discrete_series.Ici ts V min_t → set.Ici min_t → V := 
  λser t, discrete_series.Ici.sample_floor_helper t ser none


def discrete_series.Ici.sample_ceil_helper {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] {min_t : time ts}
  (v : set.Ici min_t) : discrete_series.Ici ts V min_t → option (set.Ici min_t × V) → V
| [] (none) := inhabited.default V
| [] (some t_) := t_.value
| (h::t) (some t_) := 
  if h.timestamp.val < t_.timestamp.val ∧ v.val ≤ h.timestamp.val
  then discrete_series.Ici.sample_ceil_helper t (some h) 
  else discrete_series.Ici.sample_ceil_helper t (some t_)
| (h::t) (none) := 
  if v.val ≤ h.timestamp.val
  then discrete_series.Ici.sample_ceil_helper t (some h) 
  else discrete_series.Ici.sample_ceil_helper t none


def discrete_series.Ici.sample_ceil {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] {min_t : time ts}
  : discrete_series.Ici ts V min_t → set.Ici min_t → V := 
  λser t, discrete_series.Ici.sample_ceil_helper t ser none

/-
abbreviation discrete_timestamped_series {tf : time_frame} (ts : time_space tf) (V : Type u) [inhabited V] :=
  list (timestamped ts V)

def discrete_timestamped_series.mk_empty {tf : time_frame} {ts : time_space tf} {V : Type u} 
  [inhabited V] : discrete_timestamped_series ts V := []

def discrete_timestamped_series.update {tf : time_frame} {ts : time_space tf} {V : Type u} 
  [inhabited V] :
  discrete_timestamped_series ts V → time ts → V → discrete_timestamped_series ts V
--| [] ts_ val_ := [(ts_, val_)]
--| (h::t) ts_ val_ := (h::t ++ [(ts_, val_)] :  list (timestamped ts V))
| ser ts_ val_ := ser.cons (ts_, val_)

def discrete_timestamped_series.latest_helper {tf : time_frame} {ts : time_space tf} {V : Type u}
  [inhabited V] :
  discrete_timestamped_series ts V → (timestamped ts V) → V
| (h::t) v := if h.timestamp > v.timestamp then discrete_timestamped_series.latest_helper t h else discrete_timestamped_series.latest_helper t v
| [] v := v.value

def discrete_timestamped_series.latest {tf : time_frame} {ts : time_space tf} {V : Type u} 
  [inhabited V] :
  discrete_timestamped_series ts V → V
| (h::t) := discrete_timestamped_series.latest_helper t h
| [] :=  inhabited.default V

abbreviation discrete_timestamped_series.Icc {tf : time_frame} (ts : time_space tf) (V : Type u) [inhabited V]
  (min_t max_t : time ts) :=
  list (set.Icc min_t max_t × V)

abbreviation discrete_timestamped_series.Ici {tf : time_frame} (ts : time_space tf) (V : Type u) [inhabited V]
  (min_t : time ts) :=
  list (set.Ici min_t × V)

def discrete_timestamped_series.sample  {tf : time_frame} {ts : time_space tf} {V : Type u} 
  [inhabited V] 
  : discrete_timestamped_series ts V → time ts → V
| [] t_ := inhabited.default V
| (h::t) t_ := if h.timestamp = t_ then h.value else discrete_timestamped_series.sample t t_ 

def discrete_timestamped_series.sample_floor_helper {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] 
  (v : time ts) : discrete_timestamped_series ts V → option (timestamped ts V) → V
| [] (none) := inhabited.default V
| [] (some t_) := t_.value
| (h::t) (some t_) := 
  if t_.timestamp < h.timestamp ∧ h.timestamp ≤ v 
  then discrete_timestamped_series.sample_floor_helper t (some h) 
  else discrete_timestamped_series.sample_floor_helper t (some t_)
| (h::t) (none) := 
  if h.timestamp ≤ v 
  then discrete_timestamped_series.sample_floor_helper t (some h) 
  else discrete_timestamped_series.sample_floor_helper t none


def discrete_timestamped_series.sample_floor {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] 
  : discrete_timestamped_series ts V → time ts → V := 
  λser t, discrete_timestamped_series.sample_floor_helper t ser none

def discrete_timestamped_series.sample_ceil_helper {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] 
  (v : time ts) : discrete_timestamped_series ts V → option (timestamped ts V) → V
| [] (none) := inhabited.default V
| [] (some t_) := t_.value
| (h::t) (some t_) := 
  if h.timestamp < t_.timestamp ∧ v ≤ h.timestamp
  then discrete_timestamped_series.sample_ceil_helper t (some h) 
  else discrete_timestamped_series.sample_ceil_helper t (some t_)
| (h::t) (none) := 
  if v ≤ h.timestamp 
  then discrete_timestamped_series.sample_ceil_helper t (some h) 
  else discrete_timestamped_series.sample_ceil_helper t none


def discrete_timestamped_series.sample_ceil {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] 
  : discrete_timestamped_series ts V → time ts → V := 
  λser t, discrete_timestamped_series.sample_ceil_helper t ser none

def discrete_timestamped_series.Icc.sample {min_t max_t : time ts}
  : discrete_timestamped_series.Icc ts V min_t max_t → time ts → V
| [] t_ := inhabited.default V
| (h::t) t_ := if h.timestamp.1 = t_ then h.value else discrete_timestamped_series.Icc.sample t t_ 


def discrete_timestamped_series.Icc.sample_floor_helper {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] {min_t max_t : time ts}
  (v : set.Icc min_t max_t) : discrete_timestamped_series.Icc ts V min_t max_t → option (set.Icc min_t max_t × V) → V
| [] (none) := inhabited.default V
| [] (some t_) := t_.value
| (h::t) (some t_) := 
  if t_.timestamp.val < h.timestamp ∧ h.timestamp.val ≤ v 
  then discrete_timestamped_series.Icc.sample_floor_helper t (some h) 
  else discrete_timestamped_series.Icc.sample_floor_helper t (some t_)
| (h::t) (none) := 
  if h.timestamp.val ≤ v 
  then discrete_timestamped_series.Icc.sample_floor_helper t (some h) 
  else discrete_timestamped_series.Icc.sample_floor_helper t none


def discrete_timestamped_series.Icc.sample_floor 
  {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] {min_t max_t : time ts}
  : discrete_timestamped_series.Icc ts V min_t max_t → set.Icc min_t max_t → V := 
  λser t, discrete_timestamped_series.Icc.sample_floor_helper t ser none


def discrete_timestamped_series.Icc.sample_ceil_helper {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] {min_t max_t : time ts}
  (v : set.Icc min_t max_t) : discrete_timestamped_series.Icc ts V min_t max_t → option (set.Icc min_t max_t × V) → V
| [] (none) := inhabited.default V
| [] (some t_) := t_.value
| (h::t) (some t_) := 
  if h.timestamp.val < t_.timestamp.val ∧ v.val ≤ h.timestamp.val
  then discrete_timestamped_series.Icc.sample_ceil_helper t (some h) 
  else discrete_timestamped_series.Icc.sample_ceil_helper t (some t_)
| (h::t) (none) := 
  if v.val ≤ h.timestamp.val
  then discrete_timestamped_series.Icc.sample_ceil_helper t (some h) 
  else discrete_timestamped_series.Icc.sample_ceil_helper t none


def discrete_timestamped_series.Icc.sample_ceil {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] {min_t max_t : time ts}
  : discrete_timestamped_series.Icc ts V min_t max_t → set.Icc min_t max_t → V := 
  λser t, discrete_timestamped_series.Icc.sample_ceil_helper t ser none


def discrete_timestamped_series.Ici.sample {min_t : time ts}
  : discrete_timestamped_series.Ici ts V min_t → time ts → V
| [] t_ := inhabited.default V
| (h::t) t_ := if h.timestamp.1 = t_ then h.value else discrete_timestamped_series.Ici.sample t t_ 


def discrete_timestamped_series.Ici.sample_floor_helper {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] {min_t : time ts}
  (v : set.Ici min_t) : discrete_timestamped_series.Ici ts V min_t → option (set.Ici min_t × V) → V
| [] (none) := inhabited.default V
| [] (some t_) := t_.value
| (h::t) (some t_) := 
  if t_.timestamp.val < h.timestamp ∧ h.timestamp.val ≤ v 
  then discrete_timestamped_series.Ici.sample_floor_helper t (some h) 
  else discrete_timestamped_series.Ici.sample_floor_helper t (some t_)
| (h::t) (none) := 
  if h.timestamp.val ≤ v 
  then discrete_timestamped_series.Ici.sample_floor_helper t (some h) 
  else discrete_timestamped_series.Ici.sample_floor_helper t none


def discrete_timestamped_series.Ici.sample_floor 
  {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] {min_t : time ts}
  : discrete_timestamped_series.Ici ts V min_t → set.Ici min_t → V := 
  λser t, discrete_timestamped_series.Ici.sample_floor_helper t ser none


def discrete_timestamped_series.Ici.sample_ceil_helper {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] {min_t : time ts}
  (v : set.Ici min_t) : discrete_timestamped_series.Ici ts V min_t → option (set.Ici min_t × V) → V
| [] (none) := inhabited.default V
| [] (some t_) := t_.value
| (h::t) (some t_) := 
  if h.timestamp.val < t_.timestamp.val ∧ v.val ≤ h.timestamp.val
  then discrete_timestamped_series.Ici.sample_ceil_helper t (some h) 
  else discrete_timestamped_series.Ici.sample_ceil_helper t (some t_)
| (h::t) (none) := 
  if v.val ≤ h.timestamp.val
  then discrete_timestamped_series.Ici.sample_ceil_helper t (some h) 
  else discrete_timestamped_series.Ici.sample_ceil_helper t none


def discrete_timestamped_series.Ici.sample_ceil {tf : time_frame} {ts : time_space tf} {V : Type u} [inhabited V] {min_t : time ts}
  : discrete_timestamped_series.Ici ts V min_t → set.Ici min_t → V := 
  λser t, discrete_timestamped_series.Ici.sample_ceil_helper t ser none
-/