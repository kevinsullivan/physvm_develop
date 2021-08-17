import .geom3d
import ..time.time

open_locale affine

section foo 

universes u

variables {tf : time_frame} (ts : time_space tf )

/-
All proofs are commented out for now
-/

abbreviation non_negative_time := time ts-- // x.coord >= 0}
/-@[ext]
structure geom3d_series {tf : time_frame} (ts : time_space tf ) := 
    (series: list (non_negative_time ts))
-/
@[ext]
structure geom3d_series {tf : time_frame} (ts : time_space tf ) := 
    (series: list (non_negative_time ts × geom3d_frame))
    --(ordered : ∀ i j : fin series.length, i<j → (series.nth_le i sorry).fst.val.coord > (series.nth_le j sorry).fst.val.coord)
    /--/
    Multiple constraints so we don't have to deal with options.
    We just want to guarantee that when instantiating a timestamped vector with a series of frames, 
    there definitionally will be a frame available that the vector satisfies. This is a reasonable expectation.
    Maybe double check with Dr. Elbaum
    -/
    --(non_empty: series.length > 0)
   -- (has_zero: ∃ i : fin series.length, (series.nth_le i sorry).fst.val.coord = 0)
/-
def geom3d_series.insert {tf : time_frame} {ts : time_space tf }
    : geom3d_series ts → (non_negative_time ts × geom3d_frame) → geom3d_series ts
| (⟨[],_,_,_⟩) tup := sorry
| (⟨h::[],_,_,_⟩) tup := (⟨tup::h::[],sorry,sorry,sorry⟩)
| (⟨h::t,_,_,_⟩) tup := 
    if h.fst.val.coord > tup.fst.val.coord then 
        let tail_call := geom3d_series.insert (⟨t,sorry,sorry,sorry⟩) tup in
        ⟨h::tail_call.series,sorry,sorry,sorry⟩
    else ⟨tup::h::t,sorry,sorry,sorry⟩
-/


def geom3d_series.insert {tf : time_frame} {ts : time_space tf }
    : geom3d_series ts → (non_negative_time ts × geom3d_frame) → geom3d_series ts
| (⟨[]⟩) tup := sorry
| (⟨h::[]⟩) tup := (⟨tup::h::[]⟩)
| (⟨h::t⟩) tup := 
    if h.fst.coord > tup.fst.coord then 
        let tail_call := geom3d_series.insert (⟨t⟩) tup in
        ⟨h::tail_call.series⟩
    else ⟨tup::h::t⟩

@[simp,reducible]
def find_helper : non_negative_time ts → list (non_negative_time ts × geom3d_frame) → (non_negative_time ts × geom3d_frame)
| t_ ([]) := (mk_time _ 0, geom3d_std_frame)
| t_ (h::[]) := h
| t_ (h::t) := if t_.coord > h.fst.coord then h else find_helper t_ t

@[simp,reducible]
def geom3d_series.find  {tf : time_frame} {ts : time_space tf }
   (s : geom3d_series ts) (t : non_negative_time ts) := (find_helper ts t s.series).snd

@[simp,reducible]
def geom3d_series.find_space  {tf : time_frame} {ts : time_space tf }
   (s : geom3d_series ts) (t : non_negative_time ts) := 
   spc.single (s.find t)

@[simp,reducible]
def geom3d_series.find_index  {tf : time_frame} {ts : time_space tf }
   (s : geom3d_series ts) (t : non_negative_time ts) := 
   (find_helper ts t s.series).fst

structure series_index (s : geom3d_series ts) :=
    (idx : non_negative_time ts)

instance index_is_setoid {s : geom3d_series ts} : setoid (series_index ts s) --there are infinite geom3d_space "types"
    := 
    ⟨
        λidx1 idx2, (s.find_index idx1.idx) = (s.find_index idx2.idx),
        sorry
    ⟩

#check @index_is_setoid


def lift_si (ser : geom3d_series ts) : series_index ts ser → time ts :=
  λsi, (ser.find_index si.idx)

def lift_ {ser : geom3d_series ts} := quotient.lift (lift_si ts ser ) begin 
  dsimp [has_equiv.equiv],
  unfold lift_si,
  unfold setoid.r,
 -- unfold index_rel,
  intros a b c,
  exact c,
end

@[simp,reducible]
def find_helper'' { s : geom3d_series ts} : (quotient (@index_is_setoid tf ts s )) → 
    list (non_negative_time ts × geom3d_frame) → (non_negative_time ts × geom3d_frame)
| t_ ([]) := (mk_time _ 0, geom3d_std_frame)
| t_ (h::[]) := h
| t_ (h::t) := if (lift_ ts t_).coord > h.fst.coord then h else find_helper'' t_ t

@[simp,reducible]
def geom3d_series.find''  {tf : time_frame} {ts : time_space tf }
   (s : geom3d_series ts) (t : quotient (@index_is_setoid tf ts s )) := (find_helper'' ts t s.series).snd

@[simp,reducible]
def geom3d_series.find_space''  {tf : time_frame} {ts : time_space tf }
   (s : geom3d_series ts) (t : quotient (@index_is_setoid tf ts s )) := 
   spc.single (s.find'' t)

@[simp,reducible]
def geom3d_series.find_index''  {tf : time_frame} {ts : time_space tf }
   (s : geom3d_series ts) (t : quotient (@index_is_setoid tf ts s )) := 
   (find_helper'' ts t s.series).fst


@[simp,reducible]
def find_helper' { s : geom3d_series ts} : (series_index ts s) → list (non_negative_time ts × geom3d_frame) → (non_negative_time ts × geom3d_frame)
| t_ ([]) := (mk_time _ 0, geom3d_std_frame)
| t_ (h::[]) := h
| t_ (h::t) := if t_.idx.coord > h.fst.coord then h else find_helper' t_ t

@[simp,reducible]
def geom3d_series.find'  {tf : time_frame} {ts : time_space tf }
   (s : geom3d_series ts) (t : series_index ts s) := (find_helper' ts t s.series).snd

@[simp,reducible]
def geom3d_series.find_space'  {tf : time_frame} {ts : time_space tf }
   (s : geom3d_series ts) (t : series_index ts s) := 
   spc.single (s.find' t)

@[simp,reducible]
def geom3d_series.find_index'  {tf : time_frame} {ts : time_space tf }
   (s : geom3d_series ts) (t : series_index ts s) := 
   (find_helper' ts t s.series).fst

/-
inductive geom3d_rel (series : geom3d_series ts) : time ts → time ts → Prop
| ()
-/
@[simp, reducible]
def mk_displacement3d_timefixed_at_time  
    {tf : time_frame} {ts : time_space tf }
    (s : geom3d_series ts) (t : non_negative_time ts) (k₁ k₂ k₃ : scalar) 
    := displacement3d.mk (mk_vectr (s.find_space t) ⟨[k₁,k₂,k₃],rfl⟩) 

@[simp, reducible]
def mk_displacement3d_timefixed_at_time'  
    {tf : time_frame} {ts : time_space tf }
    (s : geom3d_series ts) (t : series_index ts s) (k₁ k₂ k₃ : scalar) 
    := displacement3d.mk (mk_vectr (s.find_space' t) ⟨[k₁,k₂,k₃],rfl⟩) 

@[simp, reducible]
def mk_displacement3d_timefixed_at_time''  
    {tf : time_frame} {ts : time_space tf }
    (s : geom3d_series ts) (t : quotient (@index_is_setoid tf ts s )) (k₁ k₂ k₃ : scalar) 
    := displacement3d.mk (mk_vectr (s.find_space'' t) ⟨[k₁,k₂,k₃],rfl⟩) 

/-
def geom3d_series.insert {tf : time_frame} {ts : time_space tf }
    : geom3d_series ts → (non_negative_time ts × geom3d_frame) → geom3d_series ts
| (⟨[]⟩) tup := sorry
| (⟨h::[]⟩) tup := (⟨tup::h::[]⟩)
| (⟨h::t⟩) tup := 
    if h.fst.coord > tup.fst.coord then 
        let tail_call := geom3d_series.insert (⟨t⟩) tup in
        ⟨h::tail_call.series⟩
    else ⟨tup::h::t⟩

@[simp]
def find_helper : non_negative_time ts → list (non_negative_time ts) → (non_negative_time ts)
| t_ ([]) := (mk_time _ 0)
| t_ (h::[]) := h
| t_ (h::t) := if t_.coord > h.coord then h else find_helper t_ t

@[simp]
def geom3d_series.find  {tf : time_frame} {ts : time_space tf }
   (s : geom3d_series ts) (t : non_negative_time ts) := (find_helper ts t s.series).snd

@[simp]
def geom3d_series.find_space  {tf : time_frame} {ts : time_space tf }
   (s : geom3d_series ts) (t : non_negative_time ts) := 
   spc.single (s.find t)

@[simp]
def geom3d_series.find_index  {tf : time_frame} {ts : time_space tf }
   (s : geom3d_series ts) (t : non_negative_time ts) := 
   (find_helper ts t s.series)

-/
/-
inductive geom3d_rel (series : geom3d_series ts) : time ts → time ts → Prop
| ()
-/
@[simp]
def mk_displacement3d_timefixed_at_time  
    {tf : time_frame} {ts : time_space tf }
    (s : geom3d_series ts) (t : non_negative_time ts) (k₁ k₂ k₃ : scalar) 
    := displacement3d.mk (mk_vectr (s.find_space t) ⟨[k₁,k₂,k₃],rfl⟩) 
/-
structure series_index (s : geom3d_series ts) :=
    (idx : non_negative_time ts)

def index_rel {s : geom3d_series ts} : 
    series_index ts s → series_index ts s → Prop 
    := 
    λidx1 idx2, (s.find_index idx1.idx) = (s.find_index idx2.idx)


instance idx_is_setoid {s : geom3d_series ts} : setoid (series_index ts s) --there are infinite geom3d_space "types"
    := 
    ⟨
        index_rel ts,
        sorry
    ⟩
-/
instance {s : geom3d_series ts} : has_equiv (series_index ts s)
    := by apply_instance
/-
instance {s : geom3d_series ts} : has_equiv (series_index ts s)
    :=
    ⟨
        index_rel ts

    ⟩-/

structure position3d_timefixed {f : geom3d_frame} (s : geom3d_space f ) extends point s
@[ext] lemma position3d_timefixed.ext : ∀  {f : geom3d_frame} {s : geom3d_space f } (x y : position3d_timefixed s),
    x.to_point = y.to_point → x = y :=
    begin
        intros f s x y e,
        cases x,
        cases y,
        simp *,
        have h₁ : ({to_point := x} : position3d_timefixed s).to_point = x := rfl,
        simp [h₁] at e,
        exact e 
    end

def position3d_timefixed.coords {f : geom3d_frame} {s : geom3d_space f } (t :position3d_timefixed s) :=
    t.to_point.coords

def position3d_timefixed.x {f : geom3d_frame} {s : geom3d_space f } (t :position3d_timefixed s) : scalar :=
    (t.to_point.coords 0).coord

def position3d_timefixed.y {f : geom3d_frame} {s : geom3d_space f } (t :position3d_timefixed s) : scalar :=
    (t.to_point.coords 1).coord

def position3d_timefixed.z {f : geom3d_frame} {s : geom3d_space f } (t :position3d_timefixed s) : scalar :=
    (t.to_point.coords 2).coord



@[simp]
def mk_position3d_timefixed' {f : geom3d_frame} (s : geom3d_space f ) (p : point s) : position3d_timefixed s := position3d_timefixed.mk p  
@[simp]
def mk_position3d_timefixed {f : geom3d_frame} (s : geom3d_space f ) (k₁ k₂ k₃ : scalar) : position3d_timefixed s := position3d_timefixed.mk (mk_point s ⟨[k₁,k₂,k₃],rfl⟩) 

@[simp]
def mk_position3d_timefixed'' {f1 f2 f3 : geom1d_frame } { s1 : geom1d_space f1} {s2 : geom1d_space f2} { s3 : geom1d_space f3}
    (p1 : position1d s1) (p2 : position1d s2) (p3 : position1d s3 )
    : position3d_timefixed (mk_prod_spc (mk_prod_spc s1 s2) s3) :=
    ⟨mk_point_prod (mk_point_prod p1.to_point p2.to_point) p3.to_point⟩
    
structure displacement3d_timefixed {f : geom3d_frame} (s : geom3d_space f ) extends vectr s 
@[ext] lemma displacement3d_timefixed.ext : ∀  {f : geom3d_frame} {s : geom3d_space f } (x y : displacement3d_timefixed s),
    x.to_vectr = y.to_vectr → x = y :=
    begin
        intros f s x y e,
        cases x,
        cases y,
        simp *,
        have h₁ : ({to_vectr := x} : displacement3d_timefixed s).to_vectr = x := rfl,
        simp [h₁] at e,
        exact e 
    end

def displacement3d_timefixed.coords {f : geom3d_frame} {s : geom3d_space f } (d :displacement3d_timefixed s) :=
    d.to_vectr.coords

@[simp]
def mk_displacement3d_timefixed' {f : geom3d_frame} (s : geom3d_space f ) (v : vectr s) : displacement3d_timefixed s := displacement3d_timefixed.mk v
@[simp]
def mk_displacement3d_timefixed  {f : geom3d_frame} (s : geom3d_space f ) (k₁ k₂ k₃ : scalar) : displacement3d_timefixed s := displacement3d_timefixed.mk (mk_vectr s ⟨[k₁,k₂,k₃],rfl⟩) 

@[simp]
def mk_displacement3d_timefixed'' {f1 f2 f3 : geom1d_frame } { s1 : geom1d_space f1} {s2 : geom1d_space f2} { s3 : geom1d_space f3}
    (p1 : displacement1d s1) (p2 : displacement1d s2) (p3 : displacement1d s3 )
    : displacement3d_timefixed (mk_prod_spc (mk_prod_spc s1 s2) s3) :=
    ⟨mk_vectr_prod (mk_vectr_prod p1.to_vectr p2.to_vectr) p3.to_vectr⟩

@[simp]
def mk_geom3d_frame {parent : geom3d_frame} {s : spc scalar parent} (p : position3d_timefixed s) 
    (v0 : displacement3d_timefixed s) (v1 : displacement3d_timefixed s) (v2 : displacement3d_timefixed s)
    : geom3d_frame :=
    (mk_frame p.to_point ⟨(λi, if i = 0 then v0.to_vectr else if i = 1 then v1.to_vectr else v2.to_vectr),sorry,sorry⟩)

end foo

section bar 

/-
    *************************************
    Instantiate module scalar (vector scalar)
    *************************************
-/

namespace geom3d
variables {f : geom3d_frame} {s : geom3d_space f } 
@[simp]
def add_displacement3d_timefixed_displacement3d_timefixed (v3 v2 : displacement3d_timefixed s) : displacement3d_timefixed s := 
    mk_displacement3d_timefixed' s (v3.to_vectr + v2.to_vectr)
@[simp]
def smul_displacement3d_timefixed (k : scalar) (v : displacement3d_timefixed s) : displacement3d_timefixed s := 
    mk_displacement3d_timefixed' s (k • v.to_vectr)
@[simp]
def neg_displacement3d_timefixed (v : displacement3d_timefixed s) : displacement3d_timefixed s := 
    mk_displacement3d_timefixed' s ((-1 : scalar) • v.to_vectr)
@[simp]
def sub_displacement3d_timefixed_displacement3d_timefixed (v3 v2 : displacement3d_timefixed s) : displacement3d_timefixed s :=    -- v3-v2
    add_displacement3d_timefixed_displacement3d_timefixed v3 (neg_displacement3d_timefixed v2)

instance has_add_displacement3d_timefixed : has_add (displacement3d_timefixed s) := ⟨ add_displacement3d_timefixed_displacement3d_timefixed ⟩
lemma add_assoc_displacement3d_timefixed : ∀ a b c : displacement3d_timefixed s, a + b + c = a + (b + c) := begin
    intros,
    ext,
    --cases a,
    repeat {
    have p3 : (a + b + c).to_vec = a.to_vec + b.to_vec + c.to_vec := rfl,
    have p2 : (a + (b + c)).to_vec = a.to_vec + (b.to_vec + c.to_vec) := rfl,
    rw [p3,p2],
    cc
    },
    admit
end
instance add_semigroup_displacement3d_timefixed : add_semigroup (displacement3d_timefixed s) := ⟨ add_displacement3d_timefixed_displacement3d_timefixed, add_assoc_displacement3d_timefixed⟩ 
@[simp]
def displacement3d_timefixed_zero  := mk_displacement3d_timefixed s 0 0 0
instance has_zero_displacement3d_timefixed : has_zero (displacement3d_timefixed s) := ⟨displacement3d_timefixed_zero⟩

lemma zero_add_displacement3d_timefixed : ∀ a : displacement3d_timefixed s, 0 + a = a := 
begin
    intros,--ext,
    ext,
    admit,
   -- let h0 : (0 + a).to_vec = (0 : vectr s).to_vec + a.to_vec := rfl,
    --simp [h0],
    --exact zero_add _,
    --exact zero_add _,
end

lemma add_zero_displacement3d_timefixed : ∀ a : displacement3d_timefixed s, a + 0 = a := 
begin
    intros,ext,
    admit,
    --exact add_zero _,
    --exact add_zero _,
end

@[simp]
def nsmul_displacement3d_timefixed : ℕ → (displacement3d_timefixed s) → (displacement3d_timefixed s) 
| nat.zero v := displacement3d_timefixed_zero
--| 3 v := v
| (nat.succ n) v := (add_displacement3d_timefixed_displacement3d_timefixed) v (nsmul_displacement3d_timefixed n v)

instance add_monoid_displacement3d_timefixed : add_monoid (displacement3d_timefixed s) := ⟨ 
    -- add_semigroup
    add_displacement3d_timefixed_displacement3d_timefixed, 
    add_assoc_displacement3d_timefixed, 
    -- has_zero
    displacement3d_timefixed_zero,
    -- new structure 
    @zero_add_displacement3d_timefixed f s, 
    add_zero_displacement3d_timefixed,
    nsmul_displacement3d_timefixed
⟩

instance has_neg_displacement3d_timefixed : has_neg (displacement3d_timefixed s) := ⟨neg_displacement3d_timefixed⟩
instance has_sub_displacement3d_timefixed : has_sub (displacement3d_timefixed s) := ⟨ sub_displacement3d_timefixed_displacement3d_timefixed⟩ 
lemma sub_eq_add_neg_displacement3d_timefixed : ∀ a b : displacement3d_timefixed s, a - b = a + -b := 
begin
    intros,ext,
    refl,
end 

instance sub_neg_monoid_displacement3d_timefixed : sub_neg_monoid (displacement3d_timefixed s) := 
{
    neg := neg_displacement3d_timefixed ,
    ..(show add_monoid (displacement3d_timefixed s), by apply_instance)
}

lemma add_left_neg_displacement3d_timefixed : ∀ a : displacement3d_timefixed s, -a + a = 0 := 
begin
    intros,
    ext,
   /- repeat {
    have h0 : (-a + a).to_vec = -a.to_vec + a.to_vec := rfl,
    simp [h0],
    have : (0:vec scalar) = (0:displacement3d_timefixed s).to_vectr.to_vec := rfl,
    simp *,
    }-/
    admit,
end

instance : add_group (displacement3d_timefixed s) := {
    add_left_neg := begin
        exact add_left_neg_displacement3d_timefixed,
    end,
..(show sub_neg_monoid (displacement3d_timefixed s), by apply_instance),

}

lemma add_comm_displacement3d_timefixed : ∀ a b : displacement3d_timefixed s, a + b = b + a :=
begin
    intros,
    ext,
    /-repeat {
    have p3 : (a + b).to_vec = a.to_vec + b.to_vec:= rfl,
    have p2 : (b + a).to_vec = b.to_vec + a.to_vec := rfl,
    rw [p3,p2],
    cc
    } 
    -/
    admit,
end
instance add_comm_semigroup_displacement3d_timefixed : add_comm_semigroup (displacement3d_timefixed s) := ⟨
    -- add_semigroup
    add_displacement3d_timefixed_displacement3d_timefixed, 
    add_assoc_displacement3d_timefixed,
    add_comm_displacement3d_timefixed,
⟩

instance add_comm_monoid_displacement3d_timefixed : add_comm_monoid (displacement3d_timefixed s) := {
    add_comm := begin
        exact add_comm_displacement3d_timefixed
    end, 
    ..(show add_monoid (displacement3d_timefixed s), by apply_instance)
}

instance has_scalar_displacement3d_timefixed : has_scalar scalar (displacement3d_timefixed s) := ⟨
smul_displacement3d_timefixed,
⟩

lemma one_smul_displacement3d_timefixed : ∀ b : displacement3d_timefixed s, (1 : scalar) • b = b := begin
    intros,ext,
    /-repeat {
        have h0 : ((3:scalar) • b).to_vec = ((3:scalar)•(b.to_vec)) := rfl,
        rw [h0],
        simp *,
    }-/
    admit,
end
lemma mul_smul_displacement3d_timefixed : ∀ (x y : scalar) (b : displacement3d_timefixed s), (x * y) • b = x • y • b := 
begin
    intros,
    cases b,
    ext,
    exact mul_assoc x y _,
end

instance mul_action_displacement3d_timefixed : mul_action scalar (displacement3d_timefixed s) := ⟨
one_smul_displacement3d_timefixed,
mul_smul_displacement3d_timefixed,
⟩ 

lemma smul_add_displacement3d_timefixed : ∀(r : scalar) (x y : displacement3d_timefixed s), r • (x + y) = r • x + r • y := begin
    intros, ext,
    repeat {
    have h0 : (r • (x + y)).to_vec = (r • (x.to_vec + y.to_vec)) := rfl,
    have h3 : (r•x + r•y).to_vec = (r•x.to_vec + r•y.to_vec) := rfl,
    rw [h0,h3],
    simp *,
    }
    ,admit,
end
lemma smul_zero_displacement3d_timefixed : ∀(r : scalar), r • (0 : displacement3d_timefixed s) = 0 := begin
    admit--intros, ext, exact mul_zero _, exact mul_zero _
end
instance distrib_mul_action_K_displacement3d_timefixed : distrib_mul_action scalar (displacement3d_timefixed s) := ⟨
smul_add_displacement3d_timefixed,
smul_zero_displacement3d_timefixed,
⟩ 

-- renaming vs template due to clash with name "s" for prevailing variable
lemma add_smul_displacement3d_timefixed : ∀ (a b : scalar) (x : displacement3d_timefixed s), (a + b) • x = a • x + b • x := 
begin
  intros,
  ext,
  exact right_distrib _ _ _,
end
lemma zero_smul_displacement3d_timefixed : ∀ (x : displacement3d_timefixed s), (0 : scalar) • x = 0 := begin
    intros,
    ext,
    admit,--exact zero_mul _, exact zero_mul _
end
instance module_K_displacement3d_timefixed : module scalar (displacement3d_timefixed s) := ⟨ add_smul_displacement3d_timefixed, zero_smul_displacement3d_timefixed ⟩ 

instance add_comm_group_displacement3d_timefixed : add_comm_group (displacement3d_timefixed s) := {
    add_comm := begin
        exact add_comm_displacement3d_timefixed
    end,
..(show add_group (displacement3d_timefixed s), by apply_instance)
}
instance : module scalar (displacement3d_timefixed s) := @geom3d.module_K_displacement3d_timefixed f s


/-
    ********************
    *** Affine space ***
    ********************
-/


/-
Affine operations
-/
instance : has_add (displacement3d_timefixed s) := ⟨add_displacement3d_timefixed_displacement3d_timefixed⟩
instance : has_zero (displacement3d_timefixed s) := ⟨displacement3d_timefixed_zero⟩
instance : has_neg (displacement3d_timefixed s) := ⟨neg_displacement3d_timefixed⟩

/-
Lemmas needed to implement affine space API
-/
@[simp]
def sub_position3d_timefixed_position3d_timefixed {f : geom3d_frame} {s : geom3d_space f } (p3 p2 : position3d_timefixed s) : displacement3d_timefixed s := 
    mk_displacement3d_timefixed' s (p3.to_point -ᵥ p2.to_point)
@[simp]
def add_position3d_timefixed_displacement3d_timefixed {f : geom3d_frame} {s : geom3d_space f } (p : position3d_timefixed s) (v : displacement3d_timefixed s) : position3d_timefixed s := 
    mk_position3d_timefixed' s (v.to_vectr +ᵥ p.to_point) -- reorder assumes order is irrelevant
@[simp]
def add_displacement3d_timefixed_position3d_timefixed {f : geom3d_frame} {s : geom3d_space f } (v : displacement3d_timefixed s) (p : position3d_timefixed s) : position3d_timefixed s := 
    mk_position3d_timefixed' s (v.to_vectr +ᵥ p.to_point)
--@[simp]
--def aff_displacement3d_timefixed_group_action : displacement3d_timefixed s → position3d_timefixed s → position3d_timefixed s := add_displacement3d_timefixed_position3d_timefixed scalar
instance : has_vadd (displacement3d_timefixed s) (position3d_timefixed s) := ⟨add_displacement3d_timefixed_position3d_timefixed⟩

lemma zero_displacement3d_timefixed_vadd'_a3 : ∀ p : position3d_timefixed s, (0 : displacement3d_timefixed s) +ᵥ p = p := begin
    intros,
    ext,--exact zero_add _,
    admit--exact add_zero _
end
lemma displacement3d_timefixed_add_assoc'_a3 : ∀ (g3 g2 : displacement3d_timefixed s) (p : position3d_timefixed s), g3 +ᵥ (g2 +ᵥ p) = (g3 + g2) +ᵥ p := begin
    intros, ext,
    repeat {
    have h0 : (g3 +ᵥ (g2 +ᵥ p)).to_pt = (g3.to_vec +ᵥ (g2.to_vec +ᵥ p.to_pt)) := rfl,
    have h3 : (g3 + g2 +ᵥ p).to_pt = (g3.to_vec +ᵥ g2.to_vec +ᵥ p.to_pt) := rfl,
    rw [h0,h3],
    simp *,
    simp [has_vadd.vadd, has_add.add, add_semigroup.add, add_zero_class.add, add_monoid.add, sub_neg_monoid.add, 
        add_group.add, distrib.add, ring.add, division_ring.add],
    cc,
    },
    admit,
end


instance displacement3d_timefixed_add_action: add_action (displacement3d_timefixed s) (position3d_timefixed s) := 
⟨ zero_displacement3d_timefixed_vadd'_a3, 
begin
    let h0 := displacement3d_timefixed_add_assoc'_a3,
    intros,
    exact (h0 g₁ g₂ p).symm
end⟩ 
--@[simp]
--def aff_geom3d_group_sub : position3d_timefixed s → position3d_timefixed s → displacement3d_timefixed s := sub_geom3d_position3d_timefixed scalar
instance position3d_timefixed_has_vsub : has_vsub (displacement3d_timefixed s) (position3d_timefixed s) := ⟨ sub_position3d_timefixed_position3d_timefixed⟩ 

instance : nonempty (position3d_timefixed s) := ⟨mk_position3d_timefixed s 0 0 0⟩

lemma position3d_timefixed_vsub_vadd_a3 : ∀ (p3 p2 : (position3d_timefixed s)), (p3 -ᵥ p2) +ᵥ p2 = p3 := begin
    /-intros, ext,
    --repeat {
    have h0 : (p3 -ᵥ p2 +ᵥ p2).to_pt = (p3.to_pt -ᵥ p2.to_pt +ᵥ p2.to_pt) := rfl,
    rw h0,
    simp [has_vsub.vsub, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub],
    simp [has_vadd.vadd, has_add.add, distrib.add, ring.add, division_ring.add],
    let h0 : field.add p2.to_pt.to_prod.fst (field.sub p3.to_pt.to_prod.fst p2.to_pt.to_prod.fst) = 
            field.add (field.sub p3.to_pt.to_prod.fst p2.to_pt.to_prod.fst) p2.to_pt.to_prod.fst := add_comm _ _,
    rw h0,
    exact sub_add_cancel _ _,
    have h0 : (p3 -ᵥ p2 +ᵥ p2).to_pt = (p3.to_pt -ᵥ p2.to_pt +ᵥ p2.to_pt) := rfl,
    rw h0,
    simp [has_vsub.vsub, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub],
    simp [has_vadd.vadd, has_add.add, distrib.add, ring.add, division_ring.add],
    let h0 : field.add p2.to_pt.to_prod.snd (field.sub p3.to_pt.to_prod.snd p2.to_pt.to_prod.snd) = 
            field.add (field.sub p3.to_pt.to_prod.snd p2.to_pt.to_prod.snd) p2.to_pt.to_prod.snd := add_comm _ _,
    rw h0,
    exact sub_add_cancel _ _,-/
    admit
end
lemma position3d_timefixed_vadd_vsub_a3 : ∀ (g : displacement3d_timefixed s) (p : position3d_timefixed s), g +ᵥ p -ᵥ p = g := 
begin
    intros, ext,
    repeat {
    have h0 : ((g +ᵥ p -ᵥ p) : displacement3d_timefixed s).to_vectr = (g.to_vectr +ᵥ p.to_point -ᵥ p.to_point) := rfl,
    rw h0,
    simp *,
    }
    
end

instance aff_geom3d_torsor' : add_torsor (displacement3d_timefixed s) (position3d_timefixed s) := 
⟨ 
    begin
        exact position3d_timefixed_vsub_vadd_a3,
    end,
    begin
        exact position3d_timefixed_vadd_vsub_a3,
    end,
⟩

open_locale affine

instance : affine_space (displacement3d_timefixed s) (position3d_timefixed s) := @geom3d.aff_geom3d_torsor' f s

end geom3d -- ha ha
end bar
