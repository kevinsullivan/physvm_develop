import .geom3d
import ..time.time

open_locale affine

section foo 

universes u
#check add_maps

abbreviation geom3d_stamped_frame := 
    (mk_prod_spc (geom3d_std_space) time_std_space).frame_type
abbreviation geom3d_stamped_space (f : geom3d_stamped_frame) := spc scalar f
def geom3d_stamped_std_frame := 
    (mk_prod_spc (geom3d_std_space) time_std_space).frame
def geom3d_stamped_std_space : geom3d_stamped_space geom3d_stamped_std_frame := 
    (mk_prod_spc (geom3d_std_space) time_std_space)

structure position3d_stamped {f : geom3d_stamped_frame} (s : geom3d_stamped_space f ) extends point s
@[ext] lemma position3d_stamped.ext : ∀  {f : geom3d_stamped_frame} {s : geom3d_stamped_space f } (x y : position3d_stamped s),
    x.to_point = y.to_point → x = y :=
    begin
        intros f s x y e,
        cases x,
        cases y,
        simp *,
        have h₁ : ({to_point := x} : position3d_stamped s).to_point = x := rfl,
        simp [h₁] at e,
        exact e 
    end

def position3d_stamped.coords {f : geom3d_stamped_frame} {s : geom3d_stamped_space f } (t :position3d_stamped s) :=
    t.to_point.coords

def position3d_stamped.x {f : geom3d_stamped_frame} {s : geom3d_stamped_space f } (t :position3d_stamped s) : scalar :=
    (t.to_point.coords 0).coord

def position3d_stamped.y {f : geom3d_stamped_frame} {s : geom3d_stamped_space f } (t :position3d_stamped s) : scalar :=
    (t.to_point.coords 1).coord

def position3d_stamped.z {f : geom3d_stamped_frame} {s : geom3d_stamped_space f } (t :position3d_stamped s) : scalar :=
    (t.to_point.coords 2).coord



@[simp]
def mk_position3d_stamped' {f : geom3d_stamped_frame} (s : geom3d_stamped_space f ) (p : point s) : position3d_stamped s := position3d_stamped.mk p  
@[simp]
def mk_position3d_stamped {f : geom3d_stamped_frame} (s : geom3d_stamped_space f ) (k₁ k₂ k₃ k₄ : scalar) : position3d_stamped s := position3d_stamped.mk (mk_point s ⟨[k₁,k₂,k₃, k₄],rfl⟩) 

@[simp]
def mk_position3d_stamped'' {f1 f2 f3 : geom1d_frame } { s1 : geom1d_space f1} {s2 : geom1d_space f2} { s3 : geom1d_space f3}
    {f4 : time_frame} {s4 : time_space f4}
    (p1 : position1d s1) (p2 : position1d s2) (p3 : position1d s3 ) (p4 : time s4)
    : position3d_stamped (mk_prod_spc (mk_prod_spc (mk_prod_spc s1 s2) s3) s4) :=
    ⟨mk_point_prod (mk_point_prod (mk_point_prod p1.to_point p2.to_point) p3.to_point) p4.to_point⟩
    
structure displacement3d_stamped {f : geom3d_stamped_frame} (s : geom3d_stamped_space f ) extends vectr s 
@[ext] lemma displacement3d_stamped.ext : ∀  {f : geom3d_stamped_frame} {s : geom3d_stamped_space f } (x y : displacement3d_stamped s),
    x.to_vectr = y.to_vectr → x = y :=
    begin
        intros f s x y e,
        cases x,
        cases y,
        simp *,
        have h₁ : ({to_vectr := x} : displacement3d_stamped s).to_vectr = x := rfl,
        simp [h₁] at e,
        exact e 
    end

def displacement3d_stamped.coords {f : geom3d_stamped_frame} {s : geom3d_stamped_space f } (d :displacement3d_stamped s) :=
    d.to_vectr.coords

def displacement3d_stamped.x {f : geom3d_stamped_frame} {s : geom3d_stamped_space f } (t :displacement3d_stamped s) : scalar :=
    (t.to_vectr.coords 0).coord

def displacement3d_stamped.y {f : geom3d_stamped_frame} {s : geom3d_stamped_space f } (t :displacement3d_stamped s) : scalar :=
    (t.to_vectr.coords 1).coord

def displacement3d_stamped.z {f : geom3d_stamped_frame} {s : geom3d_stamped_space f } (t :displacement3d_stamped s) : scalar :=
    (t.to_vectr.coords 2).coord

@[simp]
def mk_displacement3d_stamped' {f : geom3d_stamped_frame} (s : geom3d_stamped_space f ) (v : vectr s) : displacement3d_stamped s := displacement3d_stamped.mk v
@[simp]
def mk_displacement3d_stamped  {f : geom3d_stamped_frame} (s : geom3d_stamped_space f ) (k₁ k₂ k₃ k₄ : scalar) 
    : displacement3d_stamped s := displacement3d_stamped.mk (mk_vectr s ⟨[k₁,k₂,k₃,k₄],rfl⟩) 

@[simp]
def mk_displacement3d_stamped'' {f1 f2 f3 : geom1d_frame } { s1 : geom1d_space f1} {s2 : geom1d_space f2} { s3 : geom1d_space f3}
    {f4 : time_frame} {s4 : time_space f4}
    (p1 : displacement1d s1) (p2 : displacement1d s2) (p3 : displacement1d s3 ) (p4 : time s4)
    : displacement3d_stamped (mk_prod_spc (mk_prod_spc (mk_prod_spc s1 s2) s3) s4) :=
    ⟨mk_vectr_prod (mk_vectr_prod (mk_vectr_prod p1.to_vectr p2.to_vectr) p3.to_vectr) (mk_vectr s4 ⟨[(p4.coords 0).coord],rfl⟩)⟩

@[simp]
def mk_geom3d_stamped_frame {parent : geom3d_stamped_frame} {s : spc scalar parent} (p : position3d_stamped s) 
    (v0 : displacement3d s) (v1 : displacement3d s) (v2 : displacement3d s)
    : geom3d_stamped_frame :=
    (mk_frame p.to_point ⟨(λi, if i = 0 then (mk_displacement3d_stamped v0.x v0.y v0.z 0) else if i = 1 then v1.to_vectr else v2.to_vectr),sorry,sorry⟩)

end foo

section bar 

#check quot
#check quotient

/-
    *************************************
    Instantiate module scalar (vector scalar)
    *************************************
-/

namespace geom3d
variables {f : geom3d_stamped_frame} {s : geom3d_stamped_space f } 
@[simp]
def add_displacement3d_stamped_displacement3d_stamped (v3 v2 : displacement3d_stamped s) : displacement3d_stamped s := 
    mk_displacement3d_stamped' s (v3.to_vectr + v2.to_vectr)
@[simp]
def smul_displacement3d_stamped (k : scalar) (v : displacement3d_stamped s) : displacement3d_stamped s := 
    mk_displacement3d_stamped' s (k • v.to_vectr)
@[simp]
def neg_displacement3d_stamped (v : displacement3d_stamped s) : displacement3d_stamped s := 
    mk_displacement3d_stamped' s ((-1 : scalar) • v.to_vectr)
@[simp]
def sub_displacement3d_stamped_displacement3d_stamped (v3 v2 : displacement3d_stamped s) : displacement3d_stamped s :=    -- v3-v2
    add_displacement3d_stamped_displacement3d_stamped v3 (neg_displacement3d_stamped v2)

instance has_add_displacement3d_stamped : has_add (displacement3d_stamped s) := ⟨ add_displacement3d_stamped_displacement3d_stamped ⟩
lemma add_assoc_displacement3d_stamped : ∀ a b c : displacement3d_stamped s, a + b + c = a + (b + c) := begin
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
instance add_semigroup_displacement3d_stamped : add_semigroup (displacement3d_stamped s) := ⟨ add_displacement3d_stamped_displacement3d_stamped, add_assoc_displacement3d_stamped⟩ 
@[simp]
def displacement3d_stamped_zero  := mk_displacement3d_stamped s 0 0 0 0
instance has_zero_displacement3d_stamped : has_zero (displacement3d_stamped s) := ⟨displacement3d_stamped_zero⟩

lemma zero_add_displacement3d_stamped : ∀ a : displacement3d_stamped s, 0 + a = a := 
begin
    intros,--ext,
    ext,
    admit,
   -- let h0 : (0 + a).to_vec = (0 : vectr s).to_vec + a.to_vec := rfl,
    --simp [h0],
    --exact zero_add _,
    --exact zero_add _,
end

lemma add_zero_displacement3d_stamped : ∀ a : displacement3d_stamped s, a + 0 = a := 
begin
    intros,ext,
    admit,
    --exact add_zero _,
    --exact add_zero _,
end

@[simp]
def nsmul_displacement3d_stamped : ℕ → (displacement3d_stamped s) → (displacement3d_stamped s) 
| nat.zero v := displacement3d_stamped_zero
--| 3 v := v
| (nat.succ n) v := (add_displacement3d_stamped_displacement3d_stamped) v (nsmul_displacement3d_stamped n v)

instance add_monoid_displacement3d_stamped : add_monoid (displacement3d_stamped s) := ⟨ 
    -- add_semigroup
    add_displacement3d_stamped_displacement3d_stamped, 
    add_assoc_displacement3d_stamped, 
    -- has_zero
    displacement3d_stamped_zero,
    -- new structure 
    @zero_add_displacement3d_stamped f s, 
    add_zero_displacement3d_stamped,
    nsmul_displacement3d_stamped
⟩

instance has_neg_displacement3d_stamped : has_neg (displacement3d_stamped s) := ⟨neg_displacement3d_stamped⟩
instance has_sub_displacement3d_stamped : has_sub (displacement3d_stamped s) := ⟨ sub_displacement3d_stamped_displacement3d_stamped⟩ 
lemma sub_eq_add_neg_displacement3d_stamped : ∀ a b : displacement3d_stamped s, a - b = a + -b := 
begin
    intros,ext,
    refl,
end 

instance sub_neg_monoid_displacement3d_stamped : sub_neg_monoid (displacement3d_stamped s) := 
{
    neg := neg_displacement3d_stamped ,
    ..(show add_monoid (displacement3d_stamped s), by apply_instance)
}

lemma add_left_neg_displacement3d_stamped : ∀ a : displacement3d_stamped s, -a + a = 0 := 
begin
    intros,
    ext,
   /- repeat {
    have h0 : (-a + a).to_vec = -a.to_vec + a.to_vec := rfl,
    simp [h0],
    have : (0:vec scalar) = (0:displacement3d_stamped s).to_vectr.to_vec := rfl,
    simp *,
    }-/
    admit,
end

instance : add_group (displacement3d_stamped s) := {
    add_left_neg := begin
        exact add_left_neg_displacement3d_stamped,
    end,
..(show sub_neg_monoid (displacement3d_stamped s), by apply_instance),

}

lemma add_comm_displacement3d_stamped : ∀ a b : displacement3d_stamped s, a + b = b + a :=
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
instance add_comm_semigroup_displacement3d_stamped : add_comm_semigroup (displacement3d_stamped s) := ⟨
    -- add_semigroup
    add_displacement3d_stamped_displacement3d_stamped, 
    add_assoc_displacement3d_stamped,
    add_comm_displacement3d_stamped,
⟩

instance add_comm_monoid_displacement3d_stamped : add_comm_monoid (displacement3d_stamped s) := {
    add_comm := begin
        exact add_comm_displacement3d_stamped
    end, 
    ..(show add_monoid (displacement3d_stamped s), by apply_instance)
}

instance has_scalar_displacement3d_stamped : has_scalar scalar (displacement3d_stamped s) := ⟨
smul_displacement3d_stamped,
⟩

lemma one_smul_displacement3d_stamped : ∀ b : displacement3d_stamped s, (1 : scalar) • b = b := begin
    intros,ext,
    /-repeat {
        have h0 : ((3:scalar) • b).to_vec = ((3:scalar)•(b.to_vec)) := rfl,
        rw [h0],
        simp *,
    }-/
    admit,
end
lemma mul_smul_displacement3d_stamped : ∀ (x y : scalar) (b : displacement3d_stamped s), (x * y) • b = x • y • b := 
begin
    intros,
    cases b,
    ext,
    exact mul_assoc x y _,
end

instance mul_action_displacement3d_stamped : mul_action scalar (displacement3d_stamped s) := ⟨
one_smul_displacement3d_stamped,
mul_smul_displacement3d_stamped,
⟩ 

lemma smul_add_displacement3d_stamped : ∀(r : scalar) (x y : displacement3d_stamped s), r • (x + y) = r • x + r • y := begin
    intros, ext,
    repeat {
    have h0 : (r • (x + y)).to_vec = (r • (x.to_vec + y.to_vec)) := rfl,
    have h3 : (r•x + r•y).to_vec = (r•x.to_vec + r•y.to_vec) := rfl,
    rw [h0,h3],
    simp *,
    }
    ,admit,
end
lemma smul_zero_displacement3d_stamped : ∀(r : scalar), r • (0 : displacement3d_stamped s) = 0 := begin
    admit--intros, ext, exact mul_zero _, exact mul_zero _
end
instance distrib_mul_action_K_displacement3d_stamped : distrib_mul_action scalar (displacement3d_stamped s) := ⟨
smul_add_displacement3d_stamped,
smul_zero_displacement3d_stamped,
⟩ 

-- renaming vs template due to clash with name "s" for prevailing variable
lemma add_smul_displacement3d_stamped : ∀ (a b : scalar) (x : displacement3d_stamped s), (a + b) • x = a • x + b • x := 
begin
  intros,
  ext,
  exact right_distrib _ _ _,
end
lemma zero_smul_displacement3d_stamped : ∀ (x : displacement3d_stamped s), (0 : scalar) • x = 0 := begin
    intros,
    ext,
    admit,--exact zero_mul _, exact zero_mul _
end
instance module_K_displacement3d_stamped : module scalar (displacement3d_stamped s) := ⟨ add_smul_displacement3d_stamped, zero_smul_displacement3d_stamped ⟩ 

instance add_comm_group_displacement3d_stamped : add_comm_group (displacement3d_stamped s) := {
    add_comm := begin
        exact add_comm_displacement3d_stamped
    end,
..(show add_group (displacement3d_stamped s), by apply_instance)
}
instance : module scalar (displacement3d_stamped s) := @geom3d.module_K_displacement3d_stamped f s


/-
    ********************
    *** Affine space ***
    ********************
-/


/-
Affine operations
-/
instance : has_add (displacement3d_stamped s) := ⟨add_displacement3d_stamped_displacement3d_stamped⟩
instance : has_zero (displacement3d_stamped s) := ⟨displacement3d_stamped_zero⟩
instance : has_neg (displacement3d_stamped s) := ⟨neg_displacement3d_stamped⟩

/-
Lemmas needed to implement affine space API
-/
@[simp]
def sub_position3d_stamped_position3d_stamped {f : geom3d_stamped_frame} {s : geom3d_stamped_space f } (p3 p2 : position3d_stamped s) : displacement3d_stamped s := 
    mk_displacement3d_stamped' s (p3.to_point -ᵥ p2.to_point)
@[simp]
def add_position3d_stamped_displacement3d_stamped {f : geom3d_stamped_frame} {s : geom3d_stamped_space f } (p : position3d_stamped s) (v : displacement3d_stamped s) : position3d_stamped s := 
    mk_position3d_stamped' s (v.to_vectr +ᵥ p.to_point) -- reorder assumes order is irrelevant
@[simp]
def add_displacement3d_stamped_position3d_stamped {f : geom3d_stamped_frame} {s : geom3d_stamped_space f } (v : displacement3d_stamped s) (p : position3d_stamped s) : position3d_stamped s := 
    mk_position3d_stamped' s (v.to_vectr +ᵥ p.to_point)
--@[simp]
--def aff_displacement3d_stamped_group_action : displacement3d_stamped s → position3d_stamped s → position3d_stamped s := add_displacement3d_stamped_position3d_stamped scalar
instance : has_vadd (displacement3d_stamped s) (position3d_stamped s) := ⟨add_displacement3d_stamped_position3d_stamped⟩

lemma zero_displacement3d_stamped_vadd'_a3 : ∀ p : position3d_stamped s, (0 : displacement3d_stamped s) +ᵥ p = p := begin
    intros,
    ext,--exact zero_add _,
    admit--exact add_zero _
end
lemma displacement3d_stamped_add_assoc'_a3 : ∀ (g3 g2 : displacement3d_stamped s) (p : position3d_stamped s), g3 +ᵥ (g2 +ᵥ p) = (g3 + g2) +ᵥ p := begin
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


instance displacement3d_stamped_add_action: add_action (displacement3d_stamped s) (position3d_stamped s) := 
⟨ zero_displacement3d_stamped_vadd'_a3, 
begin
    let h0 := displacement3d_stamped_add_assoc'_a3,
    intros,
    exact (h0 g₁ g₂ p).symm
end⟩ 
--@[simp]
--def aff_geom3d_group_sub : position3d_stamped s → position3d_stamped s → displacement3d_stamped s := sub_geom3d_position3d_stamped scalar
instance position3d_stamped_has_vsub : has_vsub (displacement3d_stamped s) (position3d_stamped s) := ⟨ sub_position3d_stamped_position3d_stamped⟩ 

instance : nonempty (position3d_stamped s) := ⟨mk_position3d_stamped s 0 0 0 0⟩

lemma position3d_stamped_vsub_vadd_a3 : ∀ (p3 p2 : (position3d_stamped s)), (p3 -ᵥ p2) +ᵥ p2 = p3 := begin
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
lemma position3d_stamped_vadd_vsub_a3 : ∀ (g : displacement3d_stamped s) (p : position3d_stamped s), g +ᵥ p -ᵥ p = g := 
begin
    intros, ext,
    repeat {
    have h0 : ((g +ᵥ p -ᵥ p) : displacement3d_stamped s).to_vectr = (g.to_vectr +ᵥ p.to_point -ᵥ p.to_point) := rfl,
    rw h0,
    simp *,
    }
    
end

instance aff_geom3d_stamped_torsor : add_torsor (displacement3d_stamped s) (position3d_stamped s) := 
⟨ 
    begin
        exact position3d_stamped_vsub_vadd_a3,
    end,
    begin
        exact position3d_stamped_vadd_vsub_a3,
    end,
⟩

open_locale affine

--instance : affine_space (displacement3d_stamped s) (position3d_stamped s) := @geom3d.aff_geom3d_torsor f s

end geom3d -- ha ha
end bar

/-
Newer version
Tradeoff - Does not directly extend from affine equiv. Base class is an equiv on points and vectrs

Extension methods are provided to directly transform Times and Duration between frames
-/
@[ext]
structure geom3d_stamped_transform {f3 : geom3d_stamped_frame} {f2 : geom3d_stamped_frame} (sp3 : geom3d_stamped_space f3) (sp2 : geom3d_stamped_space f2)
  extends fm_tr sp3 sp2

def geom3d_stamped_space.mk_geom3d_stamped_transform_to {f3 : geom3d_stamped_frame} (s3 : geom3d_stamped_space f3) : Π {f2 : geom3d_stamped_frame} (s2 : geom3d_stamped_space f2), 
        geom3d_stamped_transform s3 s2 := --(position3d_stamped s2) ≃ᵃ[scalar] (position3d_stamped s3) := 
    λ f2 s2,
        ⟨s3.fm_tr s2⟩

def geom3d_stamped_transform.symm 
    {f3 : geom3d_stamped_frame} {f2 : geom3d_stamped_frame} {sp3 : geom3d_stamped_space f3} {sp2 : geom3d_stamped_space f2} (ttr : geom3d_stamped_transform sp3 sp2)
    : geom3d_stamped_transform sp2 sp3 := ⟨(ttr.1).symm⟩


def geom3d_stamped_transform.trans 
    {f3 : geom3d_stamped_frame} {f2 : geom3d_stamped_frame} {f3 : geom3d_stamped_frame} {sp3 : geom3d_stamped_space f3} {sp2 : geom3d_stamped_space f2} {sp3 : geom3d_stamped_space f3} 
    (ttr : geom3d_stamped_transform sp3 sp2)
    : geom3d_stamped_transform sp2 sp3 → geom3d_stamped_transform sp3 sp3 := λttr_, ⟨(ttr.1).trans ttr_.1⟩

def geom3d_stamped_transform.transform_position3d_stamped
    {f3 : geom3d_stamped_frame} {s3 : geom3d_stamped_space f3}
    {f2 : geom3d_stamped_frame} {s2 : geom3d_stamped_space f2}
    (tr: geom3d_stamped_transform s3 s2 ) : position3d_stamped s3 → position3d_stamped s2 :=
    λt : position3d_stamped s3,
    ⟨tr.to_fm_tr.to_equiv t.to_point⟩

def geom3d_stamped_transform.transform_displacement3d_stamped
    {f3 : geom3d_stamped_frame} {s3 : geom3d_stamped_space f3}
    {f2 : geom3d_stamped_frame} {s2 : geom3d_stamped_space f2}
    (tr: geom3d_stamped_transform s3 s2 ) : displacement3d_stamped s3 → displacement3d_stamped s2 :=
    λd,
    let as_pt : point s3 := ⟨λi, mk_pt scalar (d.coords i).coord⟩ in
    let tr_pt := (tr.to_equiv as_pt) in
    ⟨⟨λi, mk_vec scalar (tr_pt.coords i).coord⟩⟩

 