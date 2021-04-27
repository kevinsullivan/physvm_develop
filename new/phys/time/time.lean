import ..phys_dimensions
import linear_algebra.affine_space.basic
import ...math.aff1Kcoord.aff1Kcoord_std

open_locale affine

/-
Framed points, vectors, frames
-/

section foo 

universes u --v w
variables 
{K : Type u} [field K] [inhabited K] 

/-
Add frames and (coordinate) spaces based on frames
-/


-- points in time
structure time {f : fm K TIME} (s : spc K f ) extends point s
@[ext] lemma time.ext : ∀  {f : fm K TIME} {s : spc K f } (x y : time s),
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

@[simp]
def mk_time' {f : fm K TIME} (s : spc K f ) (p : point s) : time s := time.mk p  
@[simp]
def mk_time {f : fm K TIME} (s : spc K f ) (k : K) : time s := time.mk (mk_point s k) 

-- intervals in time
structure duration {f : fm K TIME} (s : spc K f ) extends vectr s 
@[ext] lemma duration.ext : ∀  {f : fm K TIME} {s : spc K f } (x y : duration s),
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
@[simp]
def mk_duration' {f : fm K TIME} (s : spc K f ) (v : vectr s) : duration s := duration.mk v
@[simp]
def mk_duration  {f : fm K TIME} (s : spc K f ) (k : K) : duration s := duration.mk (mk_vectr s k) 

-- note that we don't extend fm
@[simp]
def mk_time_frame {parent : fm K TIME} {s : spc K parent} (p : time s) (v : duration s) :=
fm.deriv TIME (p.to_point.to_pt, v.to_vectr.to_vec) parent   -- TODO: make sure v ≠ 0

end foo

section bar 

universes u --v w
variables 
(K : Type u) [field K] [inhabited K] 

def time_std_frame : fm K TIME := fm.base TIME
def time_std_space := mk_space K (time_std_frame K)

/-
    *************************************
    Instantiate vector_space K (vector K)
    *************************************
-/

namespace time
variables {f : fm K TIME} {s : spc K f } 
@[simp]
def add_duration_duration (v1 v2 : duration s) : duration s := 
    mk_duration' s (v1.to_vectr + v2.to_vectr)
@[simp]
def smul_duration (k : K) (v : duration s) : duration s := 
    mk_duration' s (k • v.to_vectr)
@[simp]
def neg_duration (v : duration s) : duration s := 
    mk_duration' s ((-1 : K) • v.to_vectr)
@[simp]
def sub_duration_duration (v1 v2 : duration s) : duration s :=    -- v1-v2
    add_duration_duration K v1 (neg_duration K v2)

-- See unframed file for template for proving vector_space

instance has_add_duration : has_add (duration s) := ⟨ add_duration_duration K ⟩
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
instance add_semigroup_duration : add_semigroup (duration s) := ⟨ add_duration_duration K, add_assoc_duration K⟩ 
@[simp]
def duration_zero  := mk_duration s 0
instance has_zero_duration : has_zero (duration s) := ⟨duration_zero K⟩

lemma zero_add_duration : ∀ a : duration s, 0 + a = a := 
begin
    intros,--,ext,
    cases a,
    generalize h0 : (0:duration s) = tmp,
    cases tmp,

    have h1 : ({to_vectr := tmp} : duration s) + ({to_vectr := a} : duration s)= {to_vectr := tmp + a} := rfl,
    simp * at *,
    dsimp [has_zero.zero, mul_zero_class.zero, monoid_with_zero.zero,semiring.zero,ring.zero,division_ring.zero] at h0,
    --cases h0,
    simp [duration_zero K] at h0,
    cases tmp,
    cases tmp,
    have h2: ({to_prod := tmp__to_prod, inv := tmp_inv}:vec K) = {to_prod := (field.zero , field.zero ), inv := rfl} 
            := by cc,
    simp * at *,
    dsimp [has_zero.zero, mul_zero_class.zero, monoid_with_zero.zero,add_monoid.zero, sub_neg_monoid.zero, add_group.zero, semiring.zero,ring.zero,division_ring.zero],
    trivial,
end

lemma add_zero_duration : ∀ a : duration s, a + 0 = a := 
begin
    intros,ext,
    exact add_zero _,
    exact add_zero _,
end

instance add_monoid_duration : add_monoid (duration s) := ⟨ 
    -- add_semigroup
    add_duration_duration K, 
    add_assoc_duration K, 
    -- has_zero
    duration_zero K,
    -- new structure 
    @zero_add_duration K _ _ f s, 
    add_zero_duration K
⟩

instance has_neg_duration : has_neg (duration s) := ⟨neg_duration K⟩
instance has_sub_duration : has_sub (duration s) := ⟨ sub_duration_duration K⟩ 
lemma sub_eq_add_neg_duration : ∀ a b : duration s, a - b = a + -b := 
begin
    intros,ext,
    refl,refl
end 

instance sub_neg_monoid_duration : sub_neg_monoid (duration s) := ⟨ 
    add_duration_duration K, add_assoc_duration K, duration_zero K, 
    zero_add_duration K, 
    add_zero_duration K, -- add_monoid
    neg_duration K,                                                                  -- has_neg
    sub_duration_duration K,                                                              -- has_sub
    sub_eq_add_neg_duration K,                                                       -- new
⟩ 

lemma add_left_neg_duration : ∀ a : duration s, -a + a = 0 := 
begin
    intros,
    ext,
    repeat {
    have h0 : (-a + a).to_vec = -a.to_vec + a.to_vec := rfl,
    simp [h0],
    have : (0:vec K) = (0:duration s).to_vectr.to_vec := rfl,
    simp *,
    }
end

instance : add_group (duration s) := ⟨
    -- sub_neg_monoid
    add_duration_duration K, add_assoc_duration K, duration_zero K, zero_add_duration K, add_zero_duration K, -- add_monoid
    neg_duration K,                                                                  -- has_neg
    sub_duration_duration K,                                                              -- has_sub
    sub_eq_add_neg_duration K, 
    -- new
    add_left_neg_duration K,
⟩ 

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
    add_duration_duration K, 
    add_assoc_duration K,
    add_comm_duration K,
⟩

instance add_comm_monoid_duration : add_comm_monoid (duration s) := ⟨
-- add_monoid
    -- add_semigroup
    add_duration_duration K, 
    add_assoc_duration K, 
    -- has_zero
    duration_zero K,
    -- new structure 
    zero_add_duration K, 
    add_zero_duration K,
-- add_comm_semigroup (minus repeats)
    add_comm_duration K,
⟩

instance has_scalar_duration : has_scalar K (duration s) := ⟨
smul_duration K,
⟩

lemma one_smul_duration : ∀ b : duration s, (1 : K) • b = b := begin
    intros,ext,
    repeat {
        have h0 : ((1:K) • b).to_vec = ((1:K)•(b.to_vec)) := rfl,
        rw [h0],
        simp *,
    }
end
lemma mul_smul_duration : ∀ (x y : K) (b : duration s), (x * y) • b = x • y • b := 
begin
    intros,
    cases b,
    ext,
    exact mul_assoc x y _,
    exact mul_assoc x y _
end

instance mul_action_duration : mul_action K (duration s) := ⟨
one_smul_duration K,
mul_smul_duration K,
⟩ 

lemma smul_add_duration : ∀(r : K) (x y : duration s), r • (x + y) = r • x + r • y := begin
    intros, ext,
    repeat {
    have h0 : (r • (x + y)).to_vec = (r • (x.to_vec + y.to_vec)) := rfl,
    have h1 : (r•x + r•y).to_vec = (r•x.to_vec + r•y.to_vec) := rfl,
    rw [h0,h1],
    simp *,
    }

end
lemma smul_zero_duration : ∀(r : K), r • (0 : duration s) = 0 := begin
    intros, ext, exact mul_zero _, exact mul_zero _
end
instance distrib_mul_action_K_duration : distrib_mul_action K (duration s) := ⟨
smul_add_duration K,
smul_zero_duration K,
⟩ 

-- renaming vs template due to clash with name "s" for prevailing variable
lemma add_smul_duration : ∀ (a b : K) (x : duration s), (a + b) • x = a • x + b • x := 
begin
  intros,
  ext,
  exact right_distrib _ _ _,
  exact right_distrib _ _ _
end
lemma zero_smul_duration : ∀ (x : duration s), (0 : K) • x = 0 := begin
    intros,
    ext,
    exact zero_mul _, exact zero_mul _
end
instance semimodule_K_duration : semimodule K (duration s) := ⟨ add_smul_duration K, zero_smul_duration  K⟩ 

instance add_comm_group_duration : add_comm_group (duration s) := ⟨
-- add_group
    add_duration_duration K, add_assoc_duration K, duration_zero K, zero_add_duration K, add_zero_duration K, -- add_monoid
    neg_duration K,                                                                  -- has_neg
    sub_duration_duration K,                                                              -- has_sub
    sub_eq_add_neg_duration K, 
    add_left_neg_duration K,
-- commutativity
    add_comm_duration K,
⟩

instance : vector_space K (duration s) := @time.semimodule_K_duration K _ _ f s


/-
    ********************
    *** Affine space ***
    ********************
-/


/-
Affine operations
-/
instance : has_add (duration s) := ⟨add_duration_duration K⟩
instance : has_zero (duration s) := ⟨duration_zero K⟩
instance : has_neg (duration s) := ⟨neg_duration K⟩

/-
Lemmas needed to implement affine space API
-/
@[simp]
def sub_time_time {f : fm K TIME} {s : spc K f } (p1 p2 : time s) : duration s := 
    mk_duration' s (p1.to_point -ᵥ p2.to_point)
@[simp]
def add_time_duration {f : fm K TIME} {s : spc K f } (p : time s) (v : duration s) : time s := 
    mk_time' s (v.to_vectr +ᵥ p.to_point) -- reorder assumes order is irrelevant
@[simp]
def add_duration_time {f : fm K TIME} {s : spc K f } (v : duration s) (p : time s) : time s := 
    mk_time' s (v.to_vectr +ᵥ p.to_point)
--@[simp]
--def aff_duration_group_action : duration s → time s → time s := add_duration_time K
instance : has_vadd (duration s) (time s) := ⟨add_duration_time K⟩

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
    simp [has_vadd.vadd, has_add.add, add_semigroup.add, add_monoid.add, sub_neg_monoid.add, 
        add_group.add, distrib.add, ring.add, division_ring.add],
    cc,
    }
end
instance duration_add_action: add_action (duration s) (time s) := 
⟨ add_duration_time K, zero_duration_vadd'_a1 K, duration_add_assoc'_a1  K⟩ 
--@[simp]
--def aff_time_group_sub : time s → time s → duration s := sub_time_time K
instance time_has_vsub : has_vsub (duration s) (time s) := ⟨ sub_time_time K ⟩ 

instance : nonempty (time s) := ⟨mk_time s 0⟩

lemma time_vsub_vadd_a1 : ∀ (p1 p2 : (time s)), (p1 -ᵥ p2) +ᵥ p2 = p1 := begin
    intros, ext,
    repeat {
    have h0 : (p1 -ᵥ p2 +ᵥ p2).to_point = (p1.to_point -ᵥ p2.to_point +ᵥ p2.to_point) := rfl,
    rw h0,
    simp *,
    }
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

instance aff_time_torsor : add_torsor (duration s) (time s) := 
⟨ 
    add_duration_time K,
    zero_duration_vadd'_a1 K,    -- add_action
    duration_add_assoc'_a1 K,   -- add_action
    sub_time_time K,    -- has_vsub
    time_vsub_vadd_a1 K,     -- add_torsor
    time_vadd_vsub_a1 K,     -- add_torsor
⟩

open_locale affine

instance : affine_space (duration s) (time s) := @time.aff_time_torsor K _ _ f s

end time -- ha ha
end bar

--prefer implicit here
universes u
variables 
{K : Type u} [field K] [inhabited K] 


--extends does not work with abbreviation or def, so the type is ugly.

/-
Older version (3/31)

structure time_transform {K : Type u} [field K] [inhabited K] {f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2 : spc K f2)
  extends ((time sp1) ≃ᵃ[K] (time sp2))
variables {f1 : fm K TIME} {f2 : fm K TIME}  (s2 : spc K f2)
def spc.time_tr (s1 : spc K f1) {f2 : fm K TIME} : Π(s2 : spc K f2), time_transform s1 s2 := --(time s2) ≃ᵃ[K] (time s1) := 
    λ s2,
    let pointtr : (point s1) ≃ᵃ[K] (point s2)  := s1.tr s2 in
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
structure time_transform {K : Type u} [field K] [inhabited K] {f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2 : spc K f2)
  extends fm_tr sp1 sp2


def spc.time_tr {f1 : fm K TIME} (s1 : spc K f1) : Π {f2 : fm K TIME} (s2 : spc K f2), 
        time_transform s1 s2 := --(time s2) ≃ᵃ[K] (time s1) := 
    λ f2 s2,
        ⟨s1.fm_tr s2⟩
        
variables 
     {f1 : fm K TIME} {s1 : spc K f1}
     {f2 : fm K TIME} {s2 : spc K f2}
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
    (tr: time_transform s1 s2 ) : time s1 → time s2 :=
    λt : time s1,
    ⟨tr.to_fm_tr.to_equiv t.to_point⟩

def time_transform.transform_duration
    (tr: time_transform s1 s2 ) : duration s1 → duration s2 :=
    λd,
    let as_pt : point s1 := (⟨⟨(1,d.to_vectr.to_vec.to_prod.2),rfl⟩⟩) in
    let tr_pt := (tr.to_equiv as_pt) in
    ⟨⟨⟨(0, tr_pt.to_pt.to_prod.2),rfl⟩⟩⟩


def stdsp := time_std_space ℚ
variables (myd : duration stdsp) (myt : time stdsp)

#check (stdsp.fm_tr stdsp).transform_vectr myd.1
#check (stdsp.time_tr stdsp).transform_time myt
