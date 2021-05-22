import ..phys_dimensions
import linear_algebra.affine_space.basic
import ...math.aff1Kcoord.aff1Kcoord_std
import ..scalar


open_locale affine

/-
Framed points, vectors, frames
-/

section foo 

universes u --v w
--variables 
--{scalar : Type u} [field scalar] [inhabited scalar] 

/-
Add frames and (coordinate) spaces based on frames
-/


-- points in time
structure time {f : fm scalar TIME} (s : spc _ f ) extends point s
@[ext] lemma time.ext : ∀  {f : fm scalar TIME} {s : spc scalar f } (x y : time s),
    x.to_point = y.to_point → x = y :=
    begin
        intros f s x y e,
        cases x,
        cases y,
        simp *,
        have h₁ : ({to_point := x} : time s).to_point = x := rfl,
        simp [h₁] at e,
        exact e 
    end

def time.coords {f : fm scalar TIME} {s : spc scalar f } (t :time s) :=
    t.to_point.to_pt.to_prod

@[simp]
def mk_time' {f : fm scalar TIME} (s : spc scalar f ) (p : point s) : time s := time.mk p  
@[simp]
def mk_time {f : fm scalar TIME} (s : spc scalar f ) (k : scalar) : time s := time.mk (mk_point s k) 

-- intervals in time
structure duration {f : fm scalar TIME} (s : spc scalar f ) extends vectr s 
@[ext] lemma duration.ext : ∀  {f : fm scalar TIME} {s : spc scalar f } (x y : duration s),
    x.to_vectr = y.to_vectr → x = y :=
    begin
        intros f s x y e,
        cases x,
        cases y,
        simp *,
        have h₁ : ({to_vectr := x} : duration s).to_vectr = x := rfl,
        simp [h₁] at e,
        exact e 
    end


def duration.coords {f : fm scalar TIME} {s : spc scalar f } (d :duration s) :=
    d.to_vectr.to_vec.to_prod

@[simp]
def mk_duration' {f : fm scalar TIME} (s : spc scalar f ) (v : vectr s) : duration s := duration.mk v
@[simp]
def mk_duration  {f : fm scalar TIME} (s : spc scalar f ) (k : scalar) : duration s := duration.mk (mk_vectr s k) 

-- note that we don't extend fm
@[simp]
def mk_time_frame {parent : fm scalar TIME} {s : spc scalar parent} (p : time s) (v : duration s) :=
fm.deriv TIME (p.to_point.to_pt, v.to_vectr.to_vec) parent   -- TODO: make sure v ≠ 0

end foo

section bar 

--universes u --v w
--variables 
--(scalar : Type u) [field scalar] [inhabited scalar] 

def time_std_frame : fm scalar TIME := fm.base TIME
def time_std_space : spc scalar time_std_frame := mk_space scalar (time_std_frame)

/-
    *************************************
    Instantiate module scalar (vector scalar)
    *************************************
-/

namespace time
variables {f : fm scalar TIME} {s : spc scalar f } 
@[simp]
def add_duration_duration (v1 v2 : duration s) : duration s := 
    mk_duration' s (v1.to_vectr + v2.to_vectr)
@[simp]
def smul_duration (k : scalar) (v : duration s) : duration s := 
    mk_duration' s (k • v.to_vectr)
@[simp]
def neg_duration (v : duration s) : duration s := 
    mk_duration' s ((-1 : scalar) • v.to_vectr)
@[simp]
def sub_duration_duration (v1 v2 : duration s) : duration s :=    -- v1-v2
    add_duration_duration v1 (neg_duration v2)

-- See unframed file for template for proving module

instance has_add_duration : has_add (duration s) := ⟨ add_duration_duration ⟩
lemma add_assoc_duration : ∀ a b c : duration s, a + b + c = a + (b + c) := begin
    intros,
    ext,
    --cases a,
    repeat {
    have p1 : (a + b + c).to_vec = a.to_vec + b.to_vec + c.to_vec := rfl,
    have p2 : (a + (b + c)).to_vec = a.to_vec + (b.to_vec + c.to_vec) := rfl,
    rw [p1,p2],
    cc
    },

end
instance add_semigroup_duration : add_semigroup (duration s) := ⟨ add_duration_duration, add_assoc_duration⟩ 
@[simp]
def duration_zero  := mk_duration s 0
instance has_zero_duration : has_zero (duration s) := ⟨duration_zero⟩

/-
Andrew 5/14 - broke this, fix sometime soon
-/
lemma zero_add_duration : ∀ a : duration s, 0 + a = a := 
begin
    intros,--ext,
    ext,
    let h0 : (0 + a).to_vec = (0 : vectr s).to_vec + a.to_vec := rfl,
    simp [h0],
    exact zero_add _,
    exact zero_add _,
end

lemma add_zero_duration : ∀ a : duration s, a + 0 = a := 
begin
    intros,ext,
    exact add_zero _,
    exact add_zero _,
end

@[simp]
def nsmul_duration : ℕ → (duration s) → (duration s) 
| nat.zero v := duration_zero
--| 1 v := v
| (nat.succ n) v := (add_duration_duration) v (nsmul_duration n v)

instance add_monoid_duration : add_monoid (duration s) := ⟨ 
    -- add_semigroup
    add_duration_duration, 
    add_assoc_duration, 
    -- has_zero
    duration_zero,
    -- new structure 
    @zero_add_duration f s, 
    add_zero_duration,
    nsmul_duration
⟩

instance has_neg_duration : has_neg (duration s) := ⟨neg_duration⟩
instance has_sub_duration : has_sub (duration s) := ⟨ sub_duration_duration⟩ 
lemma sub_eq_add_neg_duration : ∀ a b : duration s, a - b = a + -b := 
begin
    intros,ext,
    refl,refl
end 

instance sub_neg_monoid_duration : sub_neg_monoid (duration s) := 
{
    neg := neg_duration,
    ..(show add_monoid (duration s), by apply_instance)
}
/-⟨ 
    add_duration_duration, add_assoc_duration, duration_zero, 
    zero_add_duration, 
    add_zero_duration, -- add_monoid
    neg_duration,                                                                  -- has_neg
    sub_duration_duration,                                                              -- has_sub
    sub_eq_add_neg_duration,                                                       -- new
⟩ -/

lemma add_left_neg_duration : ∀ a : duration s, -a + a = 0 := 
begin
    intros,
    ext,
    repeat {
    have h0 : (-a + a).to_vec = -a.to_vec + a.to_vec := rfl,
    simp [h0],
    have : (0:vec scalar) = (0:duration s).to_vectr.to_vec := rfl,
    simp *,
    }
end

instance : add_group (duration s) := {
    add_left_neg := begin
        exact add_left_neg_duration,
    end,
..(show sub_neg_monoid (duration s), by apply_instance),

}

/--/ ⟨
    -- sub_neg_monoid
    add_duration_duration, add_assoc_duration, duration_zero, zero_add_duration, add_zero_duration, -- add_monoid
    neg_duration,                                                                  -- has_neg
    sub_duration_duration,                                                              -- has_sub
    sub_eq_add_neg_duration, 
    -- new
    add_left_neg_duration,
⟩ -/

lemma add_comm_duration : ∀ a b : duration s, a + b = b + a :=
begin
    intros,
    ext,
    repeat {
    have p1 : (a + b).to_vec = a.to_vec + b.to_vec:= rfl,
    have p2 : (b + a).to_vec = b.to_vec + a.to_vec := rfl,
    rw [p1,p2],
    cc
    }    
end
instance add_comm_semigroup_duration : add_comm_semigroup (duration s) := ⟨
    -- add_semigroup
    add_duration_duration, 
    add_assoc_duration,
    add_comm_duration,
⟩

instance add_comm_monoid_duration : add_comm_monoid (duration s) := {
    add_comm := begin
        exact add_comm_duration
    end, 
    ..(show add_monoid (duration s), by apply_instance)
}

/-⟨
-- add_monoid
    -- add_semigroup
    add_duration_duration, 
    add_assoc_duration, 
    -- has_zero
    duration_zero,
    -- new structure 
    zero_add_duration, 
    add_zero_duration,
-- add_comm_semigroup (minus repeats)
    add_comm_duration,
⟩-/

instance has_scalar_duration : has_scalar scalar (duration s) := ⟨
smul_duration,
⟩

lemma one_smul_duration : ∀ b : duration s, (1 : scalar) • b = b := begin
    intros,ext,
    repeat {
        have h0 : ((1:scalar) • b).to_vec = ((1:scalar)•(b.to_vec)) := rfl,
        rw [h0],
        simp *,
    }
end
lemma mul_smul_duration : ∀ (x y : scalar) (b : duration s), (x * y) • b = x • y • b := 
begin
    intros,
    cases b,
    ext,
    exact mul_assoc x y _,
    exact mul_assoc x y _
end

instance mul_action_duration : mul_action scalar (duration s) := ⟨
one_smul_duration,
mul_smul_duration,
⟩ 

lemma smul_add_duration : ∀(r : scalar) (x y : duration s), r • (x + y) = r • x + r • y := begin
    intros, ext,
    repeat {
    have h0 : (r • (x + y)).to_vec = (r • (x.to_vec + y.to_vec)) := rfl,
    have h1 : (r•x + r•y).to_vec = (r•x.to_vec + r•y.to_vec) := rfl,
    rw [h0,h1],
    simp *,
    }

end
lemma smul_zero_duration : ∀(r : scalar), r • (0 : duration s) = 0 := begin
    intros, ext, exact mul_zero _, exact mul_zero _
end
instance distrib_mul_action_K_duration : distrib_mul_action scalar (duration s) := ⟨
smul_add_duration,
smul_zero_duration,
⟩ 

-- renaming vs template due to clash with name "s" for prevailing variable
lemma add_smul_duration : ∀ (a b : scalar) (x : duration s), (a + b) • x = a • x + b • x := 
begin
  intros,
  ext,
  exact right_distrib _ _ _,
  exact right_distrib _ _ _
end
lemma zero_smul_duration : ∀ (x : duration s), (0 : scalar) • x = 0 := begin
    intros,
    ext,
    exact zero_mul _, exact zero_mul _
end
instance module_K_duration : module scalar (duration s) := ⟨ add_smul_duration, zero_smul_duration ⟩ 

instance add_comm_group_duration : add_comm_group (duration s) := 
{
    add_comm := begin
        exact add_comm_duration
        
        /-intros,
        ext,
        let h0 : (a + b).to_vec = a.to_vec + b.to_vec := rfl,
        let h1 : (b + a).to_vec = b.to_vec + a.to_vec := rfl,
        rw [h0,h1],
        exact add_comm _ _,
        exact add_comm _ _,-/
    end,
--to_add_group := (show add_group (vec K), by apply_instance),
--to_add_comm_monoid := (show add_comm_monoid (vec K), by apply_instance),
..(show add_group (duration s), by apply_instance)
}
/-⟨
-- add_group
    add_duration_duration, add_assoc_duration, duration_zero, zero_add_duration, add_zero_duration, -- add_monoid
    neg_duration,                                                                  -- has_neg
    sub_duration_duration,                                                              -- has_sub
    sub_eq_add_neg_duration, 
    add_left_neg_duration,
-- commutativity
    add_comm_duration,
⟩-/

instance : module scalar (duration s) := @time.module_K_duration f s


/-
    ********************
    *** Affine space ***
    ********************
-/


/-
Affine operations
-/
instance : has_add (duration s) := ⟨add_duration_duration⟩
instance : has_zero (duration s) := ⟨duration_zero⟩
instance : has_neg (duration s) := ⟨neg_duration⟩

/-
Lemmas needed to implement affine space API
-/
@[simp]
def sub_time_time {f : fm scalar TIME} {s : spc scalar f } (p1 p2 : time s) : duration s := 
    mk_duration' s (p1.to_point -ᵥ p2.to_point)
@[simp]
def add_time_duration {f : fm scalar TIME} {s : spc scalar f } (p : time s) (v : duration s) : time s := 
    mk_time' s (v.to_vectr +ᵥ p.to_point) -- reorder assumes order is irrelevant
@[simp]
def add_duration_time {f : fm scalar TIME} {s : spc scalar f } (v : duration s) (p : time s) : time s := 
    mk_time' s (v.to_vectr +ᵥ p.to_point)
--@[simp]
--def aff_duration_group_action : duration s → time s → time s := add_duration_time scalar
instance : has_vadd (duration s) (time s) := ⟨add_duration_time⟩

lemma zero_duration_vadd'_a1 : ∀ p : time s, (0 : duration s) +ᵥ p = p := begin
    intros,
    ext,--exact zero_add _,
    exact add_zero _,
    exact add_zero _
end
lemma duration_add_assoc'_a1 : ∀ (g1 g2 : duration s) (p : time s), g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p := begin
    intros, ext,
    repeat {
    have h0 : (g1 +ᵥ (g2 +ᵥ p)).to_pt = (g1.to_vec +ᵥ (g2.to_vec +ᵥ p.to_pt)) := rfl,
    have h1 : (g1 + g2 +ᵥ p).to_pt = (g1.to_vec +ᵥ g2.to_vec +ᵥ p.to_pt) := rfl,
    rw [h0,h1],
    simp *,
    simp [has_vadd.vadd, has_add.add, add_semigroup.add, add_zero_class.add, add_monoid.add, sub_neg_monoid.add, 
        add_group.add, distrib.add, ring.add, division_ring.add],
    cc,
    }
end

instance duration_add_action: add_action (duration s) (time s) := 
⟨ zero_duration_vadd'_a1, 
begin
    let h0 := duration_add_assoc'_a1,
    intros,
    exact (h0 g₁ g₂ p).symm
end⟩ 
--@[simp]
--def aff_time_group_sub : time s → time s → duration s := sub_time_time scalar
instance time_has_vsub : has_vsub (duration s) (time s) := ⟨ sub_time_time⟩ 

instance : nonempty (time s) := ⟨mk_time s 0⟩

lemma time_vsub_vadd_a1 : ∀ (p1 p2 : (time s)), (p1 -ᵥ p2) +ᵥ p2 = p1 := begin
    intros, ext,
    --repeat {
    have h0 : (p1 -ᵥ p2 +ᵥ p2).to_pt = (p1.to_pt -ᵥ p2.to_pt +ᵥ p2.to_pt) := rfl,
    rw h0,
    simp [has_vsub.vsub, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub],
    simp [has_vadd.vadd, has_add.add, distrib.add, ring.add, division_ring.add],
    let h0 : field.add p2.to_pt.to_prod.fst (field.sub p1.to_pt.to_prod.fst p2.to_pt.to_prod.fst) = 
            field.add (field.sub p1.to_pt.to_prod.fst p2.to_pt.to_prod.fst) p2.to_pt.to_prod.fst := add_comm _ _,
    rw h0,
    exact sub_add_cancel _ _,
    have h0 : (p1 -ᵥ p2 +ᵥ p2).to_pt = (p1.to_pt -ᵥ p2.to_pt +ᵥ p2.to_pt) := rfl,
    rw h0,
    simp [has_vsub.vsub, has_sub.sub, sub_neg_monoid.sub, add_group.sub, add_comm_group.sub, ring.sub, division_ring.sub],
    simp [has_vadd.vadd, has_add.add, distrib.add, ring.add, division_ring.add],
    let h0 : field.add p2.to_pt.to_prod.snd (field.sub p1.to_pt.to_prod.snd p2.to_pt.to_prod.snd) = 
            field.add (field.sub p1.to_pt.to_prod.snd p2.to_pt.to_prod.snd) p2.to_pt.to_prod.snd := add_comm _ _,
    rw h0,
    exact sub_add_cancel _ _,
end
lemma time_vadd_vsub_a1 : ∀ (g : duration s) (p : time s), g +ᵥ p -ᵥ p = g := 
begin
    intros, ext,
    repeat {
    have h0 : ((g +ᵥ p -ᵥ p) : duration s).to_vectr = (g.to_vectr +ᵥ p.to_point -ᵥ p.to_point) := rfl,
    rw h0,
    simp *,
    }
    
end

instance aff_time_torsor : add_torsor (duration s) (time s) := ⟨
    begin
        exact time_vsub_vadd_a1,
    end,
    begin
        exact time_vadd_vsub_a1,
    end,

⟩

open_locale affine

instance : affine_space (duration s) (time s) := @time.aff_time_torsor f s

end time -- ha ha
end bar

--prefer implicit here
universes u

--extends does not work with abbreviation or def, so the type is ugly.

/-
Older version (3/31)

structure time_transform {scalar : Type u} [field scalar] [inhabited scalar] {f1 : fm scalar TIME} {f2 : fm scalar TIME} (sp1 : spc scalar f1) (sp2 : spc scalar f2)
  extends ((time sp1) ≃ᵃ[scalar] (time sp2))
variables {f1 : fm scalar TIME} {f2 : fm scalar TIME}  (s2 : spc scalar f2)
def spc.time_tr (s1 : spc scalar f1) {f2 : fm scalar TIME} : Π(s2 : spc scalar f2), time_transform s1 s2 := --(time s2) ≃ᵃ[scalar] (time s1) := 
    λ s2,
    let pointtr : (point s1) ≃ᵃ[scalar] (point s2)  := s1.tr s2 in
        ⟨⟨
            ⟨
                (λ p : time s1, (⟨(pointtr p.to_point : point _)⟩ : time s2)),
                (λ p : time s2, (⟨(pointtr.symm p.to_point : point _)⟩ : time s1)),
                sorry,
                sorry
            ⟩,
            ⟨
                (λv : duration _, (⟨(pointtr.linear v.1 : vectr _)⟩ : duration _)),
                sorry,
               -- (λ v, ⟨v.to_vec⟩),
                sorry,
                (λv : duration _, (⟨(pointtr.symm.linear v.1 : vectr _)⟩ : duration _)),
                sorry,
                sorry
            ⟩,
            sorry
        ⟩⟩
-/

/-
Newer version
Tradeoff - Does not directly extend from affine equiv. Base class is an equiv on points and vectrs

Extension methods are provided to directly transform Times and Duration between frames
-/
@[ext]
structure time_transform {f1 : fm scalar TIME} {f2 : fm scalar TIME} (sp1 : spc scalar f1) (sp2 : spc scalar f2)
  extends fm_tr sp1 sp2

def spc.mk_time_transform_to {f1 : fm scalar TIME} (s1 : spc scalar f1) : Π {f2 : fm scalar TIME} (s2 : spc scalar f2), 
        time_transform s1 s2 := --(time s2) ≃ᵃ[scalar] (time s1) := 
    λ f2 s2,
        ⟨s1.fm_tr s2⟩

/-
def fm_tr.symm  {f1 : fm K n} {f2 : fm K n} {s1 : spc K f1} {s2 : spc K f2} (ftr : fm_tr s1 s2) : fm_tr s2 s1 :=
    ⟨ftr.1.symm⟩


def fm_tr.trans  {f1 : fm K n} {f2 : fm K n} {f3 : fm K n} {s1 : spc K f1} {s2 : spc K f2} {s3 : spc K f3} (ftr : fm_tr s1 s2) : fm_tr s2 s3 → fm_tr s1 s3 :=
    λftr_, ⟨ftr.1.trans ftr_.1⟩

notation ftr⁻¹ := ftr.symm
notation ftr∘ftr2 := ftr.symm ftr2

-/

def time_transform.symm 
    {f1 : fm scalar TIME} {f2 : fm scalar TIME} {sp1 : spc scalar f1} {sp2 : spc scalar f2} (ttr : time_transform sp1 sp2)
    : time_transform sp2 sp1 := ⟨(ttr.1).symm⟩


def time_transform.trans 
    {f1 : fm scalar TIME} {f2 : fm scalar TIME} {f3 : fm scalar TIME} {sp1 : spc scalar f1} {sp2 : spc scalar f2} {sp3 : spc scalar f3} 
    (ttr : time_transform sp1 sp2)
    : time_transform sp2 sp3 → time_transform sp1 sp3 := λttr_, ⟨(ttr.1).trans ttr_.1⟩

--notation t_tr⁻¹ := (⟨⟨t_tr.fm_tr/-/⟩⟩ : time_transform _ _)
        
-- variables 
 --    {f1 : fm scalar TIME} {s1 : spc scalar f1}
 --    {f2 : fm scalar TIME} {s2 : spc scalar f2}
/-

def fm_tr.transform_point (tr:fm_tr s1 s2 ) : point s1 → point s2 :=
    λp,
    tr.to_equiv p

def fm_tr.transform_vectr (tr:fm_tr s1 s2 ) : vectr s1 → vectr s2 :=
    λv,
    let as_pt : point s1 := (⟨⟨(1,v.to_vec.to_prod.2),rfl⟩⟩) in
    let tr_pt := (tr.to_equiv as_pt) in
    ⟨⟨(0, tr_pt.to_pt.to_prod.2),rfl⟩⟩

-/

def time_transform.transform_time 
    {f1 : fm _ TIME} {s1 : spc _ f1}
    {f2 : fm _ TIME} {s2 : spc _ f2}
    (tr: time_transform s1 s2 ) : time s1 → time s2 :=
    λt : time s1,
    ⟨tr.to_fm_tr.to_equiv t.to_point⟩

def time_transform.transform_duration
    {f1 : fm _ TIME} {s1 : spc _ f1}
    {f2 : fm _ TIME} {s2 : spc _ f2}
    (tr: time_transform s1 s2 ) : duration s1 → duration s2 :=
    λd,
    let as_pt : point s1 := (⟨⟨(1,d.to_vectr.to_vec.to_prod.2),rfl⟩⟩) in
    let tr_pt := (tr.to_equiv as_pt) in
    ⟨⟨⟨(0, tr_pt.to_pt.to_prod.2),rfl⟩⟩⟩

/-
def stdsp := time_std_space
variables (myd : duration stdsp) (myt : time stdsp)


def p_2 : point (std_space ℚ 0) := mk_point (std_space ℚ 0) 5 
def v_2 : vectr (std_space ℚ 0) := mk_vectr (std_space ℚ 0) 7

def fr_1 : fm ℚ 0 := mk_frame p_2 v_2  
def space2 := mk_space ℚ fr_1 

def p_3 : point (space2) := mk_point (space2) 5 
def v_3 : vectr (space2) := mk_vectr (space2) 7

def fr_2 : fm ℚ 0 := mk_frame p_3 v_3  
def space3 := mk_space ℚ fr_2 

def tr := stdsp.mk_time_transform_to space2
def tr2 := space2.mk_time_transform_to space3
-/