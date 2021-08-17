import ..phys_dimensions
import linear_algebra.affine_space.basic
--import ...math.affnKcoord.affnKcoord_std
import ...math.euclidnK.euclidnK_definitions

import ..scalar


open_locale affine

section foo 

universes u 

abbreviation time_frame := fm scalar 1 LENGTH
abbreviation time_space (f : time_frame) := spc scalar f
noncomputable def time_std_frame : time_frame := fm.base 1 LENGTH
noncomputable def time_std_space : time_space time_std_frame := mk_space (time_std_frame)




-- points in time
structure time {f : time_frame} (s : spc _ f ) extends point s
@[ext] lemma time.ext : ∀  {f : time_frame} {s : time_space f } (x y : time s),
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

noncomputable def time.coord {f : time_frame} {s : time_space f } (t :time s): scalar :=
    (t.to_point.coords 0).coord

@[simp]
def mk_time' {f : time_frame} (s : time_space f ) (p : point s) : time s := time.mk p  
@[simp]
noncomputable def mk_time {f : time_frame} (s : time_space f ) (k : scalar) : time s := time.mk (mk_point s ⟨[k],rfl⟩) 

noncomputable instance {f : time_frame} (s : time_space f ): inhabited (time s) := ⟨mk_time _ 0⟩

-- intervals in time
structure duration {f : time_frame} (s : time_space f ) extends vectr s 
@[ext] lemma duration.ext : ∀  {f : time_frame} {s : time_space f } (x y : duration s),
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


noncomputable def duration.coord {f : time_frame} {s : time_space f } (d :duration s): scalar :=
    (d.to_vectr.coords 0).coord

@[simp]
def mk_duration' {f : time_frame} (s : time_space f ) (v : vectr s) : duration s := duration.mk v
@[simp]
noncomputable def mk_duration  {f : time_frame} (s : time_space f ) (k : scalar) : duration s := duration.mk (mk_vectr s ⟨[k],rfl⟩) 


@[simp]
noncomputable def mk_time_frame {parent : time_frame} {s : spc scalar parent} (p : time s) (v : duration s) :=
mk_frame p.to_point (vectr_basis.mk (λi, v.to_vectr) sorry sorry)   -- TODO: make sure v ≠ 0

-- Public
@[simp]
noncomputable def mk_time_space (fr : time_frame) := mk_space fr

end foo

section bar 

/-
    *************************************
    Instantiate module scalar (vector scalar)
    *************************************
-/

namespace time
variables {f : time_frame} {s : time_space f } 
@[simp]
noncomputable def add_duration_duration (v1 v2 : duration s) : duration s := 
    mk_duration' s (v1.to_vectr + v2.to_vectr)
@[simp]
noncomputable def smul_duration (k : scalar) (v : duration s) : duration s := 
    mk_duration' s (k • v.to_vectr)
@[simp]
noncomputable def neg_duration (v : duration s) : duration s := 
    mk_duration' s ((-1 : scalar) • v.to_vectr)
@[simp]
noncomputable def sub_duration_duration (v1 v2 : duration s) : duration s :=    -- v1-v2
    add_duration_duration v1 (neg_duration v2)

noncomputable instance has_add_duration : has_add (duration s) := ⟨ add_duration_duration ⟩
lemma add_assoc_duration : ∀ a b c : duration s, a + b + c = a + (b + c) := begin
    intros,
    ext,
    dsimp only [has_add.add],
    dsimp only [add_duration_duration, mk_duration', has_add.add],
    dsimp only [add_vectr_vectr, mk_vectr', has_add.add],
    dsimp only [add_vec_vec],
    simp only [add_assoc],
end
noncomputable instance add_semigroup_duration : add_semigroup (duration s) := ⟨ add_duration_duration, add_assoc_duration⟩ 
@[simp]
noncomputable def duration_zero  := mk_duration s 0
noncomputable instance has_zero_duration : has_zero (duration s) := ⟨duration_zero⟩

lemma zero_add_duration : ∀ a : duration s, 0 + a = a := 
begin
    intros,
    ext,
    dsimp only [has_zero.zero, has_add.add],
    dsimp only [add_duration_duration, duration_zero, mk_duration', mk_duration, has_add.add],
    dsimp only [add_vectr_vectr, mk_vectr', mk_vectr, mk_vec_n, has_add.add],
    dsimp only [add_vec_vec, mk_vec, vector.nth],
    simp only [list.nth_le_singleton, zero_add],
end

lemma add_zero_duration : ∀ a : duration s, a + 0 = a := 
begin
    intros,
    ext,
    dsimp only [has_zero.zero, has_add.add],
    dsimp only [add_duration_duration, duration_zero, mk_duration', mk_duration, has_add.add],
    dsimp only [add_vectr_vectr, mk_vectr', mk_vectr, mk_vec_n, has_add.add],
    dsimp only [add_vec_vec, mk_vec, vector.nth],
    simp only [list.nth_le_singleton, add_zero],
end

@[simp]
noncomputable def nsmul_duration : ℕ → (duration s) → (duration s) 
| nat.zero v := duration_zero
--| 1 v := v
| (nat.succ n) v := (add_duration_duration) v (nsmul_duration n v)

noncomputable instance add_monoid_duration : add_monoid (duration s) := ⟨ 
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

noncomputable instance has_neg_duration : has_neg (duration s) := ⟨neg_duration⟩
noncomputable instance has_sub_duration : has_sub (duration s) := ⟨ sub_duration_duration⟩ 
lemma sub_eq_add_neg_duration : ∀ a b : duration s, a - b = a + -b := 
begin
    intros,ext,
    refl,
end 

noncomputable instance sub_neg_monoid_duration : sub_neg_monoid (duration s) := 
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
    dsimp only [has_zero.zero, has_add.add, has_neg.neg],
    dsimp only [neg_duration, has_scalar.smul],
    dsimp only [add_duration_duration, smul_vectr, has_add.add, has_scalar.smul],
    dsimp only [add_vectr_vectr, smul_vec, mk_duration', mk_vectr', has_add.add],
    dsimp only [add_vec_vec],
    simp only [neg_mul_eq_neg_mul_symm, one_mul, mk_vectr, duration_zero, mk_duration, add_left_neg],
    dsimp only [mk_vec_n, mk_vec, vector.nth],
    simp only [list.nth_le_singleton]
end

noncomputable instance : add_group (duration s) := {
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
    dsimp only [has_add.add],
    dsimp only [add_duration_duration, has_add.add],
    dsimp only [add_vectr_vectr, has_add.add],
    dsimp only [add_vec_vec, mk_duration', mk_vectr'],
    simp only [add_comm],
end
noncomputable instance add_comm_semigroup_duration : add_comm_semigroup (duration s) := ⟨
    -- add_semigroup
    add_duration_duration, 
    add_assoc_duration,
    add_comm_duration,
⟩

noncomputable instance add_comm_monoid_duration : add_comm_monoid (duration s) := {
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

noncomputable instance has_scalar_duration : has_scalar scalar (duration s) := ⟨
smul_duration,
⟩

lemma one_smul_duration : ∀ b : duration s, (1 : scalar) • b = b := begin
    intros,
    ext,
    dsimp only [has_scalar.smul],
    dsimp only [smul_duration, has_scalar.smul],
    dsimp only [smul_vectr, has_scalar.smul],
    dsimp only [smul_vec, mk_duration', mk_vectr'],
    simp only [one_mul],
end
lemma mul_smul_duration : ∀ (x y : scalar) (b : duration s), (x * y) • b = x • y • b := 
begin
    intros,
    cases b,
    ext,
    exact mul_assoc x y _,
end

noncomputable instance mul_action_duration : mul_action scalar (duration s) := ⟨
one_smul_duration,
mul_smul_duration,
⟩ 

lemma smul_add_duration : ∀(r : scalar) (x y : duration s), r • (x + y) = r • x + r • y := begin
    intros,
    ext,
    dsimp only [has_scalar.smul, has_add.add],
    dsimp only [smul_duration, add_duration_duration, has_scalar.smul, has_add.add],
    dsimp only [smul_vectr, add_vectr_vectr, has_scalar.smul, has_add.add],
    dsimp only [smul_vec, add_vec_vec, mk_duration', mk_vectr'],
    simp only [distrib.left_distrib],
    refl,
end
lemma smul_zero_duration : ∀(r : scalar), r • (0 : duration s) = 0 := begin
    intros,
    ext,
    dsimp only [has_scalar.smul, has_zero.zero],
    dsimp only [smul_duration, duration_zero, has_scalar.smul],
    dsimp only [smul_vectr, has_scalar.smul],
    dsimp only [smul_vec, mk_duration', mk_vectr', mk_duration, mk_vectr, mk_vec_n, mk_vec, vector.nth],
    simp only [list.nth_le_singleton, mul_zero],
end
noncomputable instance distrib_mul_action_K_duration : distrib_mul_action scalar (duration s) := ⟨
smul_add_duration,
smul_zero_duration,
⟩ 

lemma add_smul_duration : ∀ (a b : scalar) (x : duration s), (a + b) • x = a • x + b • x := 
begin
  intros,
  ext,
  exact right_distrib _ _ _,
end
lemma zero_smul_duration : ∀ (x : duration s), (0 : scalar) • x = 0 := begin
    intros,
    ext,
    dsimp only [has_scalar.smul, has_zero.zero],
    dsimp only [smul_duration, duration_zero, has_scalar.smul],
    dsimp only [smul_vectr, has_scalar.smul],
    dsimp only [smul_vec, mk_duration', mk_vectr', mk_duration, mk_vectr, mk_vec_n, mk_vec, vector.nth],
    simp only [list.nth_le_singleton, mul_eq_zero],
    apply or.inl,
    refl,
end
noncomputable instance module_K_duration : module scalar (duration s) := ⟨ add_smul_duration, zero_smul_duration ⟩ 

noncomputable instance add_comm_group_duration : add_comm_group (duration s) := 
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

noncomputable instance : module scalar (duration s) := @time.module_K_duration f s


/-
    ********************
    *** Affine space ***
    ********************
-/


/-
Affine operations
-/
noncomputable instance : has_add (duration s) := ⟨add_duration_duration⟩
noncomputable instance : has_zero (duration s) := ⟨duration_zero⟩
noncomputable instance : has_neg (duration s) := ⟨neg_duration⟩

@[simp]
noncomputable def sub_time_time {f : time_frame} {s : time_space f } (p1 p2 : time s) : duration s := 
    mk_duration' s (p1.to_point -ᵥ p2.to_point)
@[simp]
noncomputable def add_time_duration {f : time_frame} {s : time_space f } (p : time s) (v : duration s) : time s := 
    mk_time' s (v.to_vectr +ᵥ p.to_point) -- reorder assumes order is irrelevant
@[simp]
noncomputable def add_duration_time {f : time_frame} {s : time_space f } (v : duration s) (p : time s) : time s := 
    mk_time' s (v.to_vectr +ᵥ p.to_point)
    
noncomputable instance : has_vadd (duration s) (time s) := ⟨add_duration_time⟩

lemma zero_duration_vadd'_a1 : ∀ p : time s, (0 : duration s) +ᵥ p = p := begin
    intros,
    ext,
    dsimp only [has_vadd.vadd, has_zero.zero],
    dsimp only [add_duration_time, duration_zero, has_vadd.vadd],
    dsimp only [add_vectr_point, has_vadd.vadd],
    dsimp only [aff_vec_group_action, add_vec_pt, mk_time', mk_point', mk_duration, mk_vectr, mk_vec_n, mk_vec, vector.nth],
    simp only [list.nth_le_singleton, add_zero],
end
lemma duration_add_assoc'_a1 : ∀ (g1 g2 : duration s) (p : time s), g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p := begin
    intros,
    ext,
    dsimp only [has_add.add, has_vadd.vadd],
    dsimp only [add_duration_time, add_duration_duration, has_add.add, has_vadd.vadd],
    dsimp only [add_vectr_point, add_vectr_vectr, has_add.add, has_vadd.vadd],
    dsimp only [aff_vec_group_action, add_vec_vec, add_vec_pt, mk_time', mk_point', mk_duration', mk_vectr'],
    simp only [add_assoc, add_right_inj],
    simp only [add_comm],
end

noncomputable instance duration_add_action: add_action (duration s) (time s) := 
⟨ zero_duration_vadd'_a1, 
begin
    let h0 := duration_add_assoc'_a1,
    intros,
    exact (h0 g₁ g₂ p).symm
end⟩ 

noncomputable instance time_has_vsub : has_vsub (duration s) (time s) := ⟨ sub_time_time⟩ 

instance : nonempty (time s) := ⟨mk_time s 0⟩

lemma time_vsub_vadd_a1 : ∀ (p1 p2 : (time s)), (p1 -ᵥ p2) +ᵥ p2 = p1 := begin
    intros,
    ext,
    dsimp only [has_vsub.vsub, has_vadd.vadd],
    dsimp only [add_duration_time, sub_time_time, has_vsub.vsub, has_vadd.vadd],
    dsimp only [add_vectr_point, aff_point_group_sub, sub_point_point, has_vsub.vsub, has_vadd.vadd],
    dsimp only [aff_vec_group_action, aff_point_group_sub, add_vec_pt, aff_pt_group_sub, sub_pt_pt, mk_time', mk_point', mk_duration', mk_vectr'],
    simp only [add_sub_cancel'_right],
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

noncomputable instance aff_time_torsor : add_torsor (duration s) (time s) := ⟨
    begin
        exact time_vsub_vadd_a1,
    end,
    begin
        exact time_vadd_vsub_a1,
    end,

⟩

open_locale affine

noncomputable instance : affine_space (duration s) (time s) := @time.aff_time_torsor f s

end time -- ha ha
end bar

universes u

@[ext]
structure time_transform {f1 : time_frame} {f2 : time_frame} (sp1 : time_space f1) (sp2 : time_space f2)
  extends fm_tr sp1 sp2

noncomputable def time_space.mk_time_transform_to {f1 : time_frame} (s1 : time_space f1) : Π {f2 : time_frame} (s2 : time_space f2), 
        time_transform s1 s2 := --(time s2) ≃ᵃ[scalar] (time s1) := 
    λ f2 s2,
        ⟨s1.fm_tr s2⟩

noncomputable def time_transform.symm 
    {f1 : time_frame} {f2 : time_frame} {sp1 : time_space f1} {sp2 : time_space f2} (ttr : time_transform sp1 sp2)
    : time_transform sp2 sp1 := ⟨(ttr.1).symm⟩


noncomputable def time_transform.trans 
    {f1 : time_frame} {f2 : time_frame} {f3 : time_frame} {sp1 : time_space f1} {sp2 : time_space f2} {sp3 : time_space f3} 
    (ttr : time_transform sp1 sp2)
    : time_transform sp2 sp3 → time_transform sp1 sp3 := λttr_, ⟨(ttr.1).trans ttr_.1⟩

noncomputable def time_transform.transform_time 
    {f1 : time_frame} {s1 : spc _ f1}
    {f2 : time_frame} {s2 : spc _ f2}
    (tr: time_transform s1 s2 ) : time s1 → time s2 :=
    λt : time s1,
    ⟨tr.to_fm_tr.to_equiv t.to_point⟩

noncomputable def time_transform.transform_duration
    {f1 : time_frame} {s1 : spc _ f1}
    {f2 : time_frame} {s2 : spc _ f2}
    (tr: time_transform s1 s2 ) : duration s1 → duration s2 :=
    λd,
    let as_pt : point s1 := ⟨λi, mk_pt scalar (d.coords i).coord⟩ in
    let tr_pt := (tr.to_equiv as_pt) in
    ⟨⟨λi, mk_vec scalar (tr_pt.coords i).coord⟩⟩
