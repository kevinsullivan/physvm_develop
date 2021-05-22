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


-- points in geom1d
structure position {f : fm scalar LENGTH} (s : spc _ f ) extends point s
@[ext] lemma position.ext : ∀  {f : fm scalar LENGTH} {s : spc scalar f } (x y : position s),
    x.to_point = y.to_point → x = y :=
    begin
        intros f s x y e,
        cases x,
        cases y,
        simp *,
        have h₁ : ({to_point := x} : position s).to_point = x := rfl,
        simp [h₁] at e,
        exact e 
    end

def position.coords {f : fm scalar LENGTH} {s : spc scalar f } (t :position s) :=
    t.to_point.to_pt.to_prod

@[simp]
def mk_position' {f : fm scalar LENGTH} (s : spc scalar f ) (p : point s) : position s := position.mk p  
@[simp]
def mk_position {f : fm scalar LENGTH} (s : spc scalar f ) (k : scalar) : position s := position.mk (mk_point s k) 

-- intervals in geom1d
structure displacement {f : fm scalar LENGTH} (s : spc scalar f ) extends vectr s 
@[ext] lemma displacement.ext : ∀  {f : fm scalar LENGTH} {s : spc scalar f } (x y : displacement s),
    x.to_vectr = y.to_vectr → x = y :=
    begin
        intros f s x y e,
        cases x,
        cases y,
        simp *,
        have h₁ : ({to_vectr := x} : displacement s).to_vectr = x := rfl,
        simp [h₁] at e,
        exact e 
    end


def displacement.coords {f : fm scalar LENGTH} {s : spc scalar f } (d :displacement s) :=
    d.to_vectr.to_vec.to_prod

@[simp]
def mk_displacement' {f : fm scalar LENGTH} (s : spc scalar f ) (v : vectr s) : displacement s := displacement.mk v
@[simp]
def mk_displacement  {f : fm scalar LENGTH} (s : spc scalar f ) (k : scalar) : displacement s := displacement.mk (mk_vectr s k) 

-- note that we don't extend fm
@[simp]
def mk_geom1d_frame {parent : fm scalar LENGTH} {s : spc scalar parent} (p : position s) (v : displacement s) :=
fm.deriv LENGTH (p.to_point.to_pt, v.to_vectr.to_vec) parent   -- TODO: make sure v ≠ 0

end foo

section bar 

--universes u --v w
--variables 
--(scalar : Type u) [field scalar] [inhabited scalar] 

def geom1d_std_frame : fm scalar LENGTH := fm.base LENGTH
def geom1d_std_space : spc scalar geom1d_std_frame := mk_space scalar (geom1d_std_frame)

/-
    *************************************
    Instantiate module scalar (vector scalar)
    *************************************
-/

namespace geom1d
variables {f : fm scalar LENGTH} {s : spc scalar f } 
@[simp]
def add_displacement_displacement (v1 v2 : displacement s) : displacement s := 
    mk_displacement' s (v1.to_vectr + v2.to_vectr)
@[simp]
def smul_displacement (k : scalar) (v : displacement s) : displacement s := 
    mk_displacement' s (k • v.to_vectr)
@[simp]
def neg_displacement (v : displacement s) : displacement s := 
    mk_displacement' s ((-1 : scalar) • v.to_vectr)
@[simp]
def sub_displacement_displacement (v1 v2 : displacement s) : displacement s :=    -- v1-v2
    add_displacement_displacement v1 (neg_displacement v2)

-- See unframed file for template for proving module

instance has_add_displacement : has_add (displacement s) := ⟨ add_displacement_displacement ⟩
lemma add_assoc_displacement : ∀ a b c : displacement s, a + b + c = a + (b + c) := begin
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
instance add_semigroup_displacement : add_semigroup (displacement s) := ⟨ add_displacement_displacement, add_assoc_displacement⟩ 
@[simp]
def displacement_zero  := mk_displacement s 0
instance has_zero_displacement : has_zero (displacement s) := ⟨displacement_zero⟩

/-
Andrew 5/14 - broke this, fix someposition soon
-/
lemma zero_add_displacement : ∀ a : displacement s, 0 + a = a := 
begin
    intros,--ext,
    ext,
    let h0 : (0 + a).to_vec = (0 : vectr s).to_vec + a.to_vec := rfl,
    simp [h0],
    exact zero_add _,
    exact zero_add _,
end

lemma add_zero_displacement : ∀ a : displacement s, a + 0 = a := 
begin
    intros,ext,
    exact add_zero _,
    exact add_zero _,
end

@[simp]
def nsmul_displacement : ℕ → (displacement s) → (displacement s) 
| nat.zero v := displacement_zero
--| 1 v := v
| (nat.succ n) v := (add_displacement_displacement) v (nsmul_displacement n v)

instance add_monoid_displacement : add_monoid (displacement s) := ⟨ 
    -- add_semigroup
    add_displacement_displacement, 
    add_assoc_displacement, 
    -- has_zero
    displacement_zero,
    -- new structure 
    @zero_add_displacement f s, 
    add_zero_displacement,
    nsmul_displacement
⟩

instance has_neg_displacement : has_neg (displacement s) := ⟨neg_displacement⟩
instance has_sub_displacement : has_sub (displacement s) := ⟨ sub_displacement_displacement⟩ 
lemma sub_eq_add_neg_displacement : ∀ a b : displacement s, a - b = a + -b := 
begin
    intros,ext,
    refl,refl
end 

instance sub_neg_monoid_displacement : sub_neg_monoid (displacement s) := 
{
    neg := neg_displacement ,
    ..(show add_monoid (displacement s), by apply_instance)
}

lemma add_left_neg_displacement : ∀ a : displacement s, -a + a = 0 := 
begin
    intros,
    ext,
    repeat {
    have h0 : (-a + a).to_vec = -a.to_vec + a.to_vec := rfl,
    simp [h0],
    have : (0:vec scalar) = (0:displacement s).to_vectr.to_vec := rfl,
    simp *,
    }
end

instance : add_group (displacement s) := {
    add_left_neg := begin
        exact add_left_neg_displacement,
    end,
..(show sub_neg_monoid (displacement s), by apply_instance),

}

lemma add_comm_displacement : ∀ a b : displacement s, a + b = b + a :=
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
instance add_comm_semigroup_displacement : add_comm_semigroup (displacement s) := ⟨
    -- add_semigroup
    add_displacement_displacement, 
    add_assoc_displacement,
    add_comm_displacement,
⟩

instance add_comm_monoid_displacement : add_comm_monoid (displacement s) := {
    add_comm := begin
        exact add_comm_displacement
    end, 
    ..(show add_monoid (displacement s), by apply_instance)
}

instance has_scalar_displacement : has_scalar scalar (displacement s) := ⟨
smul_displacement,
⟩

lemma one_smul_displacement : ∀ b : displacement s, (1 : scalar) • b = b := begin
    intros,ext,
    repeat {
        have h0 : ((1:scalar) • b).to_vec = ((1:scalar)•(b.to_vec)) := rfl,
        rw [h0],
        simp *,
    }
end
lemma mul_smul_displacement : ∀ (x y : scalar) (b : displacement s), (x * y) • b = x • y • b := 
begin
    intros,
    cases b,
    ext,
    exact mul_assoc x y _,
    exact mul_assoc x y _
end

instance mul_action_displacement : mul_action scalar (displacement s) := ⟨
one_smul_displacement,
mul_smul_displacement,
⟩ 

lemma smul_add_displacement : ∀(r : scalar) (x y : displacement s), r • (x + y) = r • x + r • y := begin
    intros, ext,
    repeat {
    have h0 : (r • (x + y)).to_vec = (r • (x.to_vec + y.to_vec)) := rfl,
    have h1 : (r•x + r•y).to_vec = (r•x.to_vec + r•y.to_vec) := rfl,
    rw [h0,h1],
    simp *,
    }

end
lemma smul_zero_displacement : ∀(r : scalar), r • (0 : displacement s) = 0 := begin
    intros, ext, exact mul_zero _, exact mul_zero _
end
instance distrib_mul_action_K_displacement : distrib_mul_action scalar (displacement s) := ⟨
smul_add_displacement,
smul_zero_displacement,
⟩ 

-- renaming vs template due to clash with name "s" for prevailing variable
lemma add_smul_displacement : ∀ (a b : scalar) (x : displacement s), (a + b) • x = a • x + b • x := 
begin
  intros,
  ext,
  exact right_distrib _ _ _,
  exact right_distrib _ _ _
end
lemma zero_smul_displacement : ∀ (x : displacement s), (0 : scalar) • x = 0 := begin
    intros,
    ext,
    exact zero_mul _, exact zero_mul _
end
instance module_K_displacement : module scalar (displacement s) := ⟨ add_smul_displacement, zero_smul_displacement ⟩ 

instance add_comm_group_displacement : add_comm_group (displacement s) := {
    add_comm := begin
        exact add_comm_displacement
        
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
..(show add_group (displacement s), by apply_instance)
}
instance : module scalar (displacement s) := @geom1d.module_K_displacement f s


/-
    ********************
    *** Affine space ***
    ********************
-/


/-
Affine operations
-/
instance : has_add (displacement s) := ⟨add_displacement_displacement⟩
instance : has_zero (displacement s) := ⟨displacement_zero⟩
instance : has_neg (displacement s) := ⟨neg_displacement⟩

/-
Lemmas needed to implement affine space API
-/
@[simp]
def sub_position_position {f : fm scalar LENGTH} {s : spc scalar f } (p1 p2 : position s) : displacement s := 
    mk_displacement' s (p1.to_point -ᵥ p2.to_point)
@[simp]
def add_position_displacement {f : fm scalar LENGTH} {s : spc scalar f } (p : position s) (v : displacement s) : position s := 
    mk_position' s (v.to_vectr +ᵥ p.to_point) -- reorder assumes order is irrelevant
@[simp]
def add_displacement_position {f : fm scalar LENGTH} {s : spc scalar f } (v : displacement s) (p : position s) : position s := 
    mk_position' s (v.to_vectr +ᵥ p.to_point)
--@[simp]
--def aff_displacement_group_action : displacement s → position s → position s := add_displacement_position scalar
instance : has_vadd (displacement s) (position s) := ⟨add_displacement_position⟩

lemma zero_displacement_vadd'_a1 : ∀ p : position s, (0 : displacement s) +ᵥ p = p := begin
    intros,
    ext,--exact zero_add _,
    exact add_zero _,
    exact add_zero _
end
lemma displacement_add_assoc'_a1 : ∀ (g1 g2 : displacement s) (p : position s), g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p := begin
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


instance displacement_add_action: add_action (displacement s) (position s) := 
⟨ zero_displacement_vadd'_a1, 
begin
    let h0 := displacement_add_assoc'_a1,
    intros,
    exact (h0 g₁ g₂ p).symm
end⟩ 
--@[simp]
--def aff_geom1d_group_sub : position s → position s → displacement s := sub_geom1d_position scalar
instance position_has_vsub : has_vsub (displacement s) (position s) := ⟨ sub_position_position⟩ 

instance : nonempty (position s) := ⟨mk_position s 0⟩

lemma position_vsub_vadd_a1 : ∀ (p1 p2 : (position s)), (p1 -ᵥ p2) +ᵥ p2 = p1 := begin
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
lemma position_vadd_vsub_a1 : ∀ (g : displacement s) (p : position s), g +ᵥ p -ᵥ p = g := 
begin
    intros, ext,
    repeat {
    have h0 : ((g +ᵥ p -ᵥ p) : displacement s).to_vectr = (g.to_vectr +ᵥ p.to_point -ᵥ p.to_point) := rfl,
    rw h0,
    simp *,
    }
    
end

instance aff_geom1d_torsor : add_torsor (displacement s) (position s) := 
⟨ 
    begin
        exact position_vsub_vadd_a1,
    end,
    begin
        exact position_vadd_vsub_a1,
    end,
⟩

open_locale affine

instance : affine_space (displacement s) (position s) := @geom1d.aff_geom1d_torsor f s

end geom1d -- ha ha
end bar

--prefer implicit here
--universes u
--variables 
--{scalar : Type u} [field scalar] [inhabited scalar] 


--extends does not work with abbreviation or def, so the type is ugly.

/-
Older version (3/31)

structure geom1d_transform {scalar : Type u} [field scalar] [inhabited scalar] {f1 : fm scalar LENGTH} {f2 : fm scalar LENGTH} (sp1 : spc scalar f1) (sp2 : spc scalar f2)
  extends ((position sp1) ≃ᵃ[scalar] (position sp2))
variables {f1 : fm scalar LENGTH} {f2 : fm scalar LENGTH}  (s2 : spc scalar f2)
def spc.geom1d_tr (s1 : spc scalar f1) {f2 : fm scalar LENGTH} : Π(s2 : spc scalar f2), geom1d_transform s1 s2 := --(position s2) ≃ᵃ[scalar] (position s1) := 
    λ s2,
    let pointtr : (point s1) ≃ᵃ[scalar] (point s2)  := s1.tr s2 in
        ⟨⟨
            ⟨
                (λ p : position s1, (⟨(pointtr p.to_point : point _)⟩ : position s2)),
                (λ p : position s2, (⟨(pointtr.symm p.to_point : point _)⟩ : position s1)),
                sorry,
                sorry
            ⟩,
            ⟨
                (λv : displacement _, (⟨(pointtr.linear v.1 : vectr _)⟩ : displacement _)),
                sorry,
               -- (λ v, ⟨v.to_vec⟩),
                sorry,
                (λv : displacement _, (⟨(pointtr.symm.linear v.1 : vectr _)⟩ : displacement _)),
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
structure geom1d_transform {f1 : fm scalar LENGTH} {f2 : fm scalar LENGTH} (sp1 : spc scalar f1) (sp2 : spc scalar f2)
  extends fm_tr sp1 sp2

def spc.mk_geom1d_transform_to {f1 : fm scalar LENGTH} (s1 : spc scalar f1) : Π {f2 : fm scalar LENGTH} (s2 : spc scalar f2), 
        geom1d_transform s1 s2 := --(position s2) ≃ᵃ[scalar] (position s1) := 
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

def geom1d_transform.symm 
    {f1 : fm scalar LENGTH} {f2 : fm scalar LENGTH} {sp1 : spc scalar f1} {sp2 : spc scalar f2} (ttr : geom1d_transform sp1 sp2)
    : geom1d_transform sp2 sp1 := ⟨(ttr.1).symm⟩


def geom1d_transform.trans 
    {f1 : fm scalar LENGTH} {f2 : fm scalar LENGTH} {f3 : fm scalar LENGTH} {sp1 : spc scalar f1} {sp2 : spc scalar f2} {sp3 : spc scalar f3} 
    (ttr : geom1d_transform sp1 sp2)
    : geom1d_transform sp2 sp3 → geom1d_transform sp1 sp3 := λttr_, ⟨(ttr.1).trans ttr_.1⟩

--notation t_tr⁻¹ := (⟨⟨t_tr.fm_tr/-/⟩⟩ : geom1d_transform _ _)
        
-- variables 
 --    {f1 : fm scalar LENGTH} {s1 : spc scalar f1}
 --    {f2 : fm scalar LENGTH} {s2 : spc scalar f2}
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

def geom1d_transform.transform_position
    {f1 : fm _ LENGTH} {s1 : spc _ f1}
    {f2 : fm _ LENGTH} {s2 : spc _ f2}
    (tr: geom1d_transform s1 s2 ) : position s1 → position s2 :=
    λt : position s1,
    ⟨tr.to_fm_tr.to_equiv t.to_point⟩

def geom1d_transform.transform_displacement
    {f1 : fm _ LENGTH} {s1 : spc _ f1}
    {f2 : fm _ LENGTH} {s2 : spc _ f2}
    (tr: geom1d_transform s1 s2 ) : displacement s1 → displacement s2 :=
    λd,
    let as_pt : point s1 := (⟨⟨(1,d.to_vectr.to_vec.to_prod.2),rfl⟩⟩) in
    let tr_pt := (tr.to_equiv as_pt) in
    ⟨⟨⟨(0, tr_pt.to_pt.to_prod.2),rfl⟩⟩⟩

/-
def stdsp := geom1d_std_space
variables (myd : displacement stdsp) (myt : position stdsp)


def p_2 : point (geom1d_std_space) := mk_point (geom1d_std_space) 5 
def v_2 : vectr (geom1d_std_space) := mk_vectr (geom1d_std_space) 7

def fr_1 : fm scalar LENGTH := mk_frame p_2 v_2  
def space2 := mk_space scalar fr_1 

def p_3 : point (space2) := mk_point (space2) 5 
def v_3 : vectr (space2) := mk_vectr (space2) 7

def fr_2 : fm scalar 1 := mk_frame p_3 v_3  
def space3 := mk_space scalar fr_2 

def tr := @spc.mk_geom1d_transform_to geom1d_std_frame stdsp fr_1 space2
def tr2 := space2.mk_geom1d_transform_to space3 
-/