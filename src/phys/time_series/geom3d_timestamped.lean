import ..geom.geom3d

open_locale affine

section foo 

universes u
#check add_maps

abbreviation geom3d_frame := 
    (mk_prod_spc (mk_prod_spc geom1d_std_space geom1d_std_space) geom1d_std_space).frame_type
abbreviation geom3d_space (f : geom3d_frame) := spc real_scalar f
noncomputable def geom3d_std_frame := 
    (mk_prod_spc (mk_prod_spc geom1d_std_space geom1d_std_space) geom1d_std_space).frame
noncomputable def geom3d_std_space : geom3d_space geom3d_std_frame := 
    (mk_prod_spc (mk_prod_spc geom1d_std_space geom1d_std_space) geom1d_std_space)

--@[reducible, elab_with_expected_type]
/-
def geom3d_std_frame : geom3d_frame := (let eqpf : 
  (add_maps 
    (add_maps 
      (λi : fin 1, LENGTH) (λi : fin 1, LENGTH)) (λi : fin 1, LENGTH)) = 
        LENGTH :=
    by simp * in
  (eq.rec_on eqpf (mk_prod_spc (mk_prod_spc geom1d_std_space geom1d_std_space) geom1d_std_space).fm) : fm real_scalar 3 LENGTH)
-/

/-
def ppp := mk_prod_spc (mk_prod_spc geom1d_std_space geom1d_std_space) geom1d_std_space

#check (merge_prod_fm (merge_prod_fm geom1d_std_frame geom1d_std_frame) geom1d_std_frame)

example : ppp.fm = geom3d_std_frame := 

#check spc.rec_on

#check @spc.rec_on real_scalar _ _ (λ dim, λ id_vec, λf, λ sp,)

#check eq.rec

#check homogeneous

def geom3d_std_space : geom3d_space (_ : geom3d_frame) := 
    begin
        let v : spc real_scalar (_ : fm real_scalar (1 + 1 + 1) (add_maps (add_maps ↑LENGTH ↑LENGTH) ↑LENGTH)) := 
            mk_prod_spc (mk_prod_spc geom1d_std_space geom1d_std_space) geom1d_std_space,
        let f := v.fm,
        let : v.frame_type = fm real_scalar (1 + 1 + 1) (add_maps (add_maps ↑LENGTH ↑LENGTH) ↑LENGTH) := rfl,
        let : v.frame_type = geom3d_frame := begin
            let eqf : (add_maps 
    (add_maps 
      (λi : fin 1, LENGTH) (λi : fin 1, LENGTH)) (λi : fin 1, LENGTH)) = (λ i:fin 3, LENGTH) := by simp *,
            simp *,
            refl
        end,
        let h : fm real_scalar (1 + 1 + 1) (add_maps (add_maps ↑LENGTH ↑LENGTH) ↑LENGTH) = geom3d_frame 
            := begin simp *,
                refl    
            end,
        let fm_ := v.fm,
        simp * at v,
        let fm_g : geom3d_frame := eq.rec fm_ (begin
            
        end),
        let vg : geom3d_space geom3d_frame := eq.rec v (by cc)
        let : v.fm = geom3d_std_frame := rfl,


        exact v,
    end
-/

structure position3d {f : geom3d_frame} (s : geom3d_space f ) extends point s
@[ext] lemma position3d.ext : ∀  {f : geom3d_frame} {s : geom3d_space f } (x y : position3d s),
    x.to_point = y.to_point → x = y :=
    begin
        intros f s x y e,
        cases x,
        cases y,
        simp *,
        have h₁ : ({to_point := x} : position3d s).to_point = x := rfl,
        simp [h₁] at e,
        exact e 
    end

noncomputable def position3d.coords {f : geom3d_frame} {s : geom3d_space f } (t :position3d s) :=
    t.to_point.coords

noncomputable def position3d.x {f : geom3d_frame} {s : geom3d_space f } (t :position3d s) : real_scalar :=
    (t.to_point.coords 0).coord

noncomputable def position3d.y {f : geom3d_frame} {s : geom3d_space f } (t :position3d s) : real_scalar :=
    (t.to_point.coords 1).coord

noncomputable def position3d.z {f : geom3d_frame} {s : geom3d_space f } (t :position3d s) : real_scalar :=
    (t.to_point.coords 2).coord



@[simp]
def mk_position3d' {f : geom3d_frame} (s : geom3d_space f ) (p : point s) : position3d s := position3d.mk p  
@[simp]
noncomputable def mk_position3d {f : geom3d_frame} (s : geom3d_space f ) (k₁ k₂ k₃ : real_scalar) : position3d s := position3d.mk (mk_point s ⟨[k₁,k₂,k₃],rfl⟩) 

@[simp]
noncomputable def mk_position3d'' {f1 f2 f3 : geom1d_frame } { s1 : geom1d_space f1} {s2 : geom1d_space f2} { s3 : geom1d_space f3}
    (p1 : position1d s1) (p2 : position1d s2) (p3 : position1d s3 )
    : position3d (mk_prod_spc (mk_prod_spc s1 s2) s3) :=
    ⟨mk_point_prod (mk_point_prod p1.to_point p2.to_point) p3.to_point⟩
    
structure displacement3d {f : geom3d_frame} (s : geom3d_space f ) extends vectr s 
@[ext] lemma displacement3d.ext : ∀  {f : geom3d_frame} {s : geom3d_space f } (x y : displacement3d s),
    x.to_vectr = y.to_vectr → x = y :=
    begin
        intros f s x y e,
        cases x,
        cases y,
        simp *,
        have h₁ : ({to_vectr := x} : displacement3d s).to_vectr = x := rfl,
        simp [h₁] at e,
        exact e 
    end



def displacement3d.frame {f : geom3d_frame} {s : geom3d_space f } (d :displacement3d s) :=
    f

noncomputable def displacement3d.coords {f : geom3d_frame} {s : geom3d_space f } (d :displacement3d s) :=
    d.to_vectr.coords

@[simp]
def mk_displacement3d' {f : geom3d_frame} (s : geom3d_space f ) (v : vectr s) : displacement3d s := displacement3d.mk v
@[simp]
noncomputable def mk_displacement3d  {f : geom3d_frame} (s : geom3d_space f ) (k₁ k₂ k₃ : real_scalar) : displacement3d s := displacement3d.mk (mk_vectr s ⟨[k₁,k₂,k₃],rfl⟩) 

@[simp]
noncomputable def mk_displacement3d'' {f1 f2 f3 : geom1d_frame } { s1 : geom1d_space f1} {s2 : geom1d_space f2} { s3 : geom1d_space f3}
    (p1 : displacement1d s1) (p2 : displacement1d s2) (p3 : displacement1d s3 )
    : displacement3d (mk_prod_spc (mk_prod_spc s1 s2) s3) :=
    ⟨mk_vectr_prod (mk_vectr_prod p1.to_vectr p2.to_vectr) p3.to_vectr⟩

@[simp]
noncomputable def mk_geom3d_frame {parent : geom3d_frame} {s : spc real_scalar parent} (p : position3d s) 
    (v0 : displacement3d s) (v1 : displacement3d s) (v2 : displacement3d s)
    : geom3d_frame :=
    (mk_frame p.to_point ⟨(λi, if i = 0 then v0.to_vectr else if i = 1 then v1.to_vectr else v2.to_vectr),sorry,sorry⟩)

@[simp]
noncomputable def mk_geom3d_space (fr : geom3d_frame) := mk_space fr


end foo

section bar 

/-
    *************************************
    Instantiate module real_scalar (vector real_scalar)
    *************************************
-/

namespace geom3d
variables {f : geom3d_frame} {s : geom3d_space f } 
@[simp]
noncomputable def add_displacement3d_displacement3d (v3 v2 : displacement3d s) : displacement3d s := 
    mk_displacement3d' s (v3.to_vectr + v2.to_vectr)
@[simp]
noncomputable def smul_displacement3d (k : real_scalar) (v : displacement3d s) : displacement3d s := 
    mk_displacement3d' s (k • v.to_vectr)
@[simp]
noncomputable def neg_displacement3d (v : displacement3d s) : displacement3d s := 
    mk_displacement3d' s ((-1 : real_scalar) • v.to_vectr)
@[simp]
noncomputable def sub_displacement3d_displacement3d (v3 v2 : displacement3d s) : displacement3d s :=    -- v3-v2
    add_displacement3d_displacement3d v3 (neg_displacement3d v2)

noncomputable instance has_add_displacement3d : has_add (displacement3d s) := ⟨ add_displacement3d_displacement3d ⟩
lemma add_assoc_displacement3d : ∀ a b c : displacement3d s, a + b + c = a + (b + c) := begin
    intros,
    ext,
    dsimp only [has_add.add],
    dsimp only [add_displacement3d_displacement3d, has_add.add],
    dsimp only [add_vectr_vectr, has_add.add],
    dsimp only [add_vec_vec, mk_displacement3d', mk_vectr'],
    simp only [add_assoc],
end
noncomputable instance add_semigroup_displacement3d : add_semigroup (displacement3d s) := ⟨ add_displacement3d_displacement3d, add_assoc_displacement3d⟩ 
@[simp]
noncomputable def displacement3d_zero  := mk_displacement3d s 0 0 0
noncomputable instance : inhabited (displacement3d s) := ⟨displacement3d_zero⟩
noncomputable instance has_zero_displacement3d : has_zero (displacement3d s) := ⟨displacement3d_zero⟩

lemma zero_add_displacement3d : ∀ a : displacement3d s, 0 + a = a := 
begin
    intros,
    ext,
    dsimp only [has_zero.zero, has_add.add],
    dsimp only [add_displacement3d_displacement3d, displacement3d_zero, mk_displacement3d', mk_displacement3d, has_add.add],
    dsimp only [add_vectr_vectr, mk_vectr', mk_vectr, mk_vec_n, has_add.add],
    dsimp only [add_vec_vec, mk_vec, vector.nth],
    cases x,
    dsimp only [fin.mk],
    cases x_val with x',
    simp only [list.nth_le, zero_add],
    simp only [add_left_eq_self, list.nth_le],
    cases x' with x'',
    simp only [list.nth_le, zero_add],
    simp only [add_left_eq_self, list.nth_le],
    cases x'' with x''',
    simp only [list.nth_le, zero_add],
    have h₀ : x'''.succ.succ.succ = x''' + 3 := rfl,
    have h₁ : 1 + 1 + 1 = 0 + 3 := rfl,
    rw [h₀, h₁] at x_property,
    have h₂ : x'''.succ + 3 ≤ 0 + 3 := begin
        dsimp only [has_lt.lt, nat.lt] at x_property,
        dsimp only [has_le.le],
        exact x_property,
    end,
    have h₃ := (add_le_add_iff_right 3).1 h₂,
    simp only [nat.not_succ_le_zero] at h₃,
    contradiction,
end

lemma add_zero_displacement3d : ∀ a : displacement3d s, a + 0 = a := 
begin
    intros,
    ext,
    dsimp only [has_zero.zero, has_add.add],
    dsimp only [add_displacement3d_displacement3d, displacement3d_zero, mk_displacement3d', mk_displacement3d, has_add.add],
    dsimp only [add_vectr_vectr, mk_vectr', mk_vectr, mk_vec_n, has_add.add],
    dsimp only [add_vec_vec, mk_vec, vector.nth],
    cases x,
    dsimp only [fin.mk],
    cases x_val with x',
    simp only [list.nth_le, add_zero],
    simp only [add_left_eq_self, list.nth_le],
    cases x' with x'',
    simp only [list.nth_le, add_zero],
    simp only [add_left_eq_self, list.nth_le],
    cases x'' with x''',
    simp only [list.nth_le, add_zero],
    have h₀ : x'''.succ.succ.succ = x''' + 3 := rfl,
    have h₁ : 1 + 1 + 1 = 0 + 3 := rfl,
    rw [h₀, h₁] at x_property,
    have h₂ : x'''.succ + 3 ≤ 0 + 3 := begin
        dsimp only [has_lt.lt, nat.lt] at x_property,
        dsimp only [has_le.le],
        exact x_property,
    end,
    have h₃ := (add_le_add_iff_right 3).1 h₂,
    simp only [nat.not_succ_le_zero] at h₃,
    contradiction,
end

@[simp]
noncomputable def nsmul_displacement3d : ℕ → (displacement3d s) → (displacement3d s) 
| nat.zero v := displacement3d_zero
--| 3 v := v
| (nat.succ n) v := (add_displacement3d_displacement3d) v (nsmul_displacement3d n v)

noncomputable instance add_monoid_displacement3d : add_monoid (displacement3d s) := ⟨ 
    -- add_semigroup
    add_displacement3d_displacement3d, 
    add_assoc_displacement3d, 
    -- has_zero
    displacement3d_zero,
    -- new structure 
    @zero_add_displacement3d f s, 
    add_zero_displacement3d,
    nsmul_displacement3d,
    begin
        admit
    end,
    begin
        admit
    end
⟩

noncomputable instance has_neg_displacement3d : has_neg (displacement3d s) := ⟨neg_displacement3d⟩
noncomputable instance has_sub_displacement3d : has_sub (displacement3d s) := ⟨ sub_displacement3d_displacement3d⟩ 
lemma sub_eq_add_neg_displacement3d : ∀ a b : displacement3d s, a - b = a + -b := 
begin
    intros,ext,
    refl,
end 

noncomputable instance sub_neg_monoid_displacement3d : sub_neg_monoid (displacement3d s) := 
{
    neg := neg_displacement3d ,
    ..(show add_monoid (displacement3d s), by apply_instance)
}

lemma add_left_neg_displacement3d : ∀ a : displacement3d s, -a + a = 0 := 
begin
    intros,
    ext,
    dsimp only [has_zero.zero, has_add.add, has_neg.neg],
    dsimp only [neg_displacement3d, has_scalar.smul],
    dsimp only [add_displacement3d_displacement3d, smul_vectr, has_add.add, has_scalar.smul],
    dsimp only [add_vectr_vectr, smul_vec, mk_displacement3d', mk_vectr', has_add.add],
    dsimp only [add_vec_vec],
    simp only [neg_mul_eq_neg_mul_symm, one_mul, mk_vectr, displacement3d_zero, mk_displacement3d, add_left_neg],
    dsimp only [mk_vec_n, mk_vec, vector.nth],
    cases x,
    dsimp only [fin.mk],
    cases x_val with x',
    simp only [list.nth_le],
    simp only [add_left_eq_self, list.nth_le],
    cases x' with x'',
    simp only [list.nth_le],
    simp only [add_left_eq_self, list.nth_le],
    cases x'' with x''',
    simp only [list.nth_le],
    have h₀ : x'''.succ.succ.succ = x''' + 3 := rfl,
    have h₁ : 1 + 1 + 1 = 0 + 3 := rfl,
    rw [h₀, h₁] at x_property,
    have h₂ : x'''.succ + 3 ≤ 0 + 3 := begin
        dsimp only [has_lt.lt, nat.lt] at x_property,
        dsimp only [has_le.le],
        exact x_property,
    end,
    have h₃ := (add_le_add_iff_right 3).1 h₂,
    simp only [nat.not_succ_le_zero] at h₃,
    contradiction,
end

noncomputable instance : add_group (displacement3d s) := {
    add_left_neg := begin
        exact add_left_neg_displacement3d,
    end,
..(show sub_neg_monoid (displacement3d s), by apply_instance),

}

lemma add_comm_displacement3d : ∀ a b : displacement3d s, a + b = b + a :=
begin
    intros,
    ext,
    dsimp only [has_add.add],
    dsimp only [add_displacement3d_displacement3d, has_add.add],
    dsimp only [add_vectr_vectr, has_add.add],
    dsimp only [add_vec_vec, mk_displacement3d', mk_vectr'],
    simp only [add_comm],
end
noncomputable instance add_comm_semigroup_displacement3d : add_comm_semigroup (displacement3d s) := ⟨
    -- add_semigroup
    add_displacement3d_displacement3d, 
    add_assoc_displacement3d,
    add_comm_displacement3d,
⟩

noncomputable instance add_comm_monoid_displacement3d : add_comm_monoid (displacement3d s) := {
    add_comm := begin
        exact add_comm_displacement3d
    end, 
    ..(show add_monoid (displacement3d s), by apply_instance)
}

noncomputable instance has_scalar_displacement3d : has_scalar real_scalar (displacement3d s) := ⟨
smul_displacement3d,
⟩

lemma one_smul_displacement3d : ∀ b : displacement3d s, (1 : real_scalar) • b = b := begin
    intros,
    ext,
    dsimp only [has_scalar.smul],
    dsimp only [smul_displacement3d, has_scalar.smul],
    dsimp only [smul_vectr, has_scalar.smul],
    dsimp only [smul_vec, mk_displacement3d', mk_vectr'],
    simp only [one_mul],
end
lemma mul_smul_displacement3d : ∀ (x y : real_scalar) (b : displacement3d s), (x * y) • b = x • y • b := 
begin
    intros,
    cases b,
    ext,
    exact mul_assoc x y _,
end

noncomputable instance mul_action_displacement3d : mul_action real_scalar (displacement3d s) := ⟨
one_smul_displacement3d,
mul_smul_displacement3d,
⟩ 

lemma smul_add_displacement3d : ∀(r : real_scalar) (x y : displacement3d s), r • (x + y) = r • x + r • y := begin
    intros,
    ext,
    dsimp only [has_scalar.smul, has_add.add],
    dsimp only [smul_displacement3d, add_displacement3d_displacement3d, has_scalar.smul, has_add.add],
    dsimp only [smul_vectr, add_vectr_vectr, has_scalar.smul, has_add.add],
    dsimp only [smul_vec, add_vec_vec, mk_displacement3d', mk_vectr'],
    simp only [distrib.left_distrib],
    refl,
end
lemma smul_zero_displacement3d : ∀(r : real_scalar), r • (0 : displacement3d s) = 0 := begin
    intros,
    ext,
    dsimp only [has_scalar.smul, has_zero.zero],
    dsimp only [smul_displacement3d, displacement3d_zero, has_scalar.smul],
    dsimp only [smul_vectr, has_scalar.smul],
    dsimp only [smul_vec, mk_displacement3d', mk_vectr', mk_displacement3d, mk_vectr, mk_vec_n, mk_vec, vector.nth],
    cases x,
    dsimp only [fin.mk],
    cases x_val with x',
    simp only [list.nth_le, mul_zero],
    simp only [list.nth_le],
    cases x' with x'',
    simp only [list.nth_le, mul_zero],
    simp only [list.nth_le],
    cases x'' with x''',
    simp only [list.nth_le, mul_zero],
    have h₀ : x'''.succ.succ.succ = x''' + 3 := rfl,
    have h₁ : 1 + 1 + 1 = 0 + 3 := rfl,
    rw [h₀, h₁] at x_property,
    have h₂ : x'''.succ + 3 ≤ 0 + 3 := begin
        dsimp only [has_lt.lt, nat.lt] at x_property,
        dsimp only [has_le.le],
        exact x_property,
    end,
    have h₃ := (add_le_add_iff_right 3).1 h₂,
    simp only [nat.not_succ_le_zero] at h₃,
    contradiction,
end
noncomputable instance distrib_mul_action_K_displacement3d : distrib_mul_action real_scalar (displacement3d s) := ⟨
smul_add_displacement3d,
smul_zero_displacement3d,
⟩ 

-- renaming vs template due to clash with name "s" for prevailing variable
lemma add_smul_displacement3d : ∀ (a b : real_scalar) (x : displacement3d s), (a + b) • x = a • x + b • x := 
begin
  intros,
  ext,
  exact right_distrib _ _ _,
end
lemma zero_smul_displacement3d : ∀ (x : displacement3d s), (0 : real_scalar) • x = 0 := begin
    intros,
    ext,
    dsimp only [has_scalar.smul, has_zero.zero],
    dsimp only [smul_displacement3d, displacement3d_zero, has_scalar.smul],
    dsimp only [smul_vectr, has_scalar.smul],
    dsimp only [smul_vec, mk_displacement3d', mk_vectr', mk_displacement3d, mk_vectr, mk_vec_n, mk_vec, vector.nth],
    cases x_1,
    dsimp only [fin.mk],
    cases x_1_val with x',
    simp only [list.nth_le, mul_eq_zero],
    apply or.inl,
    refl,
    simp only [list.nth_le],
    cases x' with x'',
    simp only [list.nth_le, mul_eq_zero],
    apply or.inl,
    refl,
    simp only [list.nth_le],
    cases x'' with x''',
    simp only [list.nth_le, mul_eq_zero],
    apply or.inl,
    refl,
    have h₀ : x'''.succ.succ.succ = x''' + 3 := rfl,
    have h₁ : 1 + 1 + 1 = 0 + 3 := rfl,
    rw [h₀, h₁] at x_1_property,
    have h₂ : x'''.succ + 3 ≤ 0 + 3 := begin
        dsimp only [has_lt.lt, nat.lt] at x_1_property,
        dsimp only [has_le.le],
        exact x_1_property,
    end,
    have h₃ := (add_le_add_iff_right 3).1 h₂,
    simp only [nat.not_succ_le_zero] at h₃,
    contradiction,
end
noncomputable instance module_K_displacement3d : module real_scalar (displacement3d s) := ⟨ add_smul_displacement3d, zero_smul_displacement3d ⟩ 

noncomputable instance add_comm_group_displacement3d : add_comm_group (displacement3d s) := {
    add_comm := begin
        exact add_comm_displacement3d
    end,
..(show add_group (displacement3d s), by apply_instance)
}
noncomputable instance : module real_scalar (displacement3d s) := @geom3d.module_K_displacement3d f s


/-
    ********************
    *** Affine space ***
    ********************
-/


/-
Affine operations
-/
noncomputable instance : has_add (displacement3d s) := ⟨add_displacement3d_displacement3d⟩
noncomputable instance : has_zero (displacement3d s) := ⟨displacement3d_zero⟩
noncomputable instance : has_neg (displacement3d s) := ⟨neg_displacement3d⟩

/-
Lemmas needed to implement affine space API
-/
@[simp]
noncomputable def sub_position3d_position3d {f : geom3d_frame} {s : geom3d_space f } (p3 p2 : position3d s) : displacement3d s := 
    mk_displacement3d' s (p3.to_point -ᵥ p2.to_point)
@[simp]
noncomputable def add_position3d_displacement3d {f : geom3d_frame} {s : geom3d_space f } (p : position3d s) (v : displacement3d s) : position3d s := 
    mk_position3d' s (v.to_vectr +ᵥ p.to_point) -- reorder assumes order is irrelevant
@[simp]
noncomputable def add_displacement3d_position3d {f : geom3d_frame} {s : geom3d_space f } (v : displacement3d s) (p : position3d s) : position3d s := 
    mk_position3d' s (v.to_vectr +ᵥ p.to_point)
--@[simp]
--def aff_displacement3d_group_action : displacement3d s → position3d s → position3d s := add_displacement3d_position3d real_scalar
noncomputable instance : has_vadd (displacement3d s) (position3d s) := ⟨add_displacement3d_position3d⟩

lemma zero_displacement3d_vadd'_a3 : ∀ p : position3d s, (0 : displacement3d s) +ᵥ p = p := begin
    intros,
    ext,
    dsimp only [has_vadd.vadd, has_zero.zero],
    dsimp only [add_displacement3d_position3d, displacement3d_zero, has_vadd.vadd],
    dsimp only [add_vectr_point, has_vadd.vadd],
    dsimp only [aff_vec_group_action, add_vec_pt, mk_position3d', mk_point', mk_displacement3d, mk_vectr, mk_vec_n, mk_vec, vector.nth],
    cases x,
    dsimp only [fin.mk],
    cases x_val with x',
    simp only [list.nth_le, add_zero],
    simp only [list.nth_le],
    cases x' with x'',
    simp only [list.nth_le, add_zero],
    simp only [list.nth_le],
    cases x'' with x''',
    simp only [list.nth_le, add_zero],
    have h₀ : x'''.succ.succ.succ = x''' + 3 := rfl,
    have h₁ : 1 + 1 + 1 = 0 + 3 := rfl,
    rw [h₀, h₁] at x_property,
    have h₂ : x'''.succ + 3 ≤ 0 + 3 := begin
        dsimp only [has_lt.lt, nat.lt] at x_property,
        dsimp only [has_le.le],
        exact x_property,
    end,
    have h₃ := (add_le_add_iff_right 3).1 h₂,
    simp only [nat.not_succ_le_zero] at h₃,
    contradiction,
end
lemma displacement3d_add_assoc'_a3 : ∀ (g3 g2 : displacement3d s) (p : position3d s), g3 +ᵥ (g2 +ᵥ p) = (g3 + g2) +ᵥ p := begin
    intros,
    ext,
    dsimp only [has_add.add, has_vadd.vadd],
    dsimp only [add_displacement3d_position3d, add_displacement3d_displacement3d, has_add.add, has_vadd.vadd],
    dsimp only [add_vectr_point, add_vectr_vectr, has_add.add, has_vadd.vadd],
    dsimp only [aff_vec_group_action, add_vec_vec, add_vec_pt, mk_position3d', mk_point', mk_displacement3d', mk_vectr'],
    simp only [add_assoc, add_right_inj],
    simp only [add_comm],
end


noncomputable instance displacement3d_add_action: add_action (displacement3d s) (position3d s) := 
⟨ zero_displacement3d_vadd'_a3, 
begin
    let h0 := displacement3d_add_assoc'_a3,
    intros,
    exact (h0 g₁ g₂ p).symm
end⟩ 
--@[simp]
--def aff_geom3d_group_sub : position3d s → position3d s → displacement3d s := sub_geom3d_position3d real_scalar
noncomputable instance position3d_has_vsub : has_vsub (displacement3d s) (position3d s) := ⟨ sub_position3d_position3d⟩ 

instance : nonempty (position3d s) := ⟨mk_position3d s 0 0 0⟩
noncomputable instance : inhabited (position3d s) := ⟨mk_position3d s 0 0 0⟩

lemma position3d_vsub_vadd_a3 : ∀ (p3 p2 : (position3d s)), (p3 -ᵥ p2) +ᵥ p2 = p3 := begin
    intros,
    ext,
    dsimp only [has_vsub.vsub, has_vadd.vadd],
    dsimp only [add_displacement3d_position3d, sub_position3d_position3d, has_vsub.vsub, has_vadd.vadd],
    dsimp only [add_vectr_point, aff_point_group_sub, sub_point_point, has_vsub.vsub, has_vadd.vadd],
    dsimp only [aff_vec_group_action, aff_point_group_sub, add_vec_pt, aff_pt_group_sub, sub_pt_pt, mk_position3d', mk_point', mk_displacement3d', mk_vectr'],
    simp only [add_sub_cancel'_right],
end
lemma position3d_vadd_vsub_a3 : ∀ (g : displacement3d s) (p : position3d s), g +ᵥ p -ᵥ p = g := 
begin
    intros, ext,
    repeat {
    have h0 : ((g +ᵥ p -ᵥ p) : displacement3d s).to_vectr = (g.to_vectr +ᵥ p.to_point -ᵥ p.to_point) := rfl,
    rw h0,
    simp *,
    }
    
end

noncomputable instance aff_geom3d_torsor : add_torsor (displacement3d s) (position3d s) := 
⟨ 
    begin
        exact position3d_vsub_vadd_a3,
    end,
    begin
        exact position3d_vadd_vsub_a3,
    end,
⟩

open_locale affine

noncomputable instance : affine_space (displacement3d s) (position3d s) := @geom3d.aff_geom3d_torsor f s

end geom3d -- ha ha
end bar

/-
Newer version
Tradeoff - Does not directly extend from affine equiv. Base class is an equiv on points and vectrs

Extension methods are provided to directly transform Times and Duration between frames
-/
@[ext]
structure geom3d_transform {f3 : geom3d_frame} {f2 : geom3d_frame} (sp3 : geom3d_space f3) (sp2 : geom3d_space f2)
  extends fm_tr sp3 sp2


noncomputable def geom3d_space.mk_geom3d_transform_to {f3 : geom3d_frame} (s3 : geom3d_space f3) : Π {f2 : geom3d_frame} (s2 : geom3d_space f2), 
        geom3d_transform s3 s2 := --(position3d s2) ≃ᵃ[scalar] (position3d s3) := 
    λ f2 s2,
        ⟨s3.fm_tr s2⟩


noncomputable instance g3tr_inh {f3 : geom3d_frame} {f2 : geom3d_frame} (sp3 : geom3d_space f3) (sp2 : geom3d_space f2) 
    : inhabited (geom3d_transform  sp3 sp2) := ⟨sp3.mk_geom3d_transform_to sp2⟩


noncomputable def geom3d_transform.symm 
    {f3 : geom3d_frame} {f2 : geom3d_frame} {sp3 : geom3d_space f3} {sp2 : geom3d_space f2} (ttr : geom3d_transform sp3 sp2)
    : geom3d_transform sp2 sp3 := ⟨(ttr.1).symm⟩


noncomputable def geom3d_transform.trans 
    {f3 : geom3d_frame} {f2 : geom3d_frame} {f3 : geom3d_frame} {sp3 : geom3d_space f3} {sp2 : geom3d_space f2} {sp3 : geom3d_space f3} 
    (ttr : geom3d_transform sp3 sp2)
    : geom3d_transform sp2 sp3 → geom3d_transform sp3 sp3 := λttr_, ⟨(ttr.1).trans ttr_.1⟩

noncomputable def geom3d_transform.transform_position3d
    {f3 : geom3d_frame} {s3 : geom3d_space f3}
    {f2 : geom3d_frame} {s2 : geom3d_space f2}
    (tr: geom3d_transform s3 s2 ) : position3d s3 → position3d s2 :=
    λt : position3d s3,
    ⟨tr.to_fm_tr.to_equiv t.to_point⟩

noncomputable def geom3d_transform.transform_displacement3d
    {f3 : geom3d_frame} {s3 : geom3d_space f3}
    {f2 : geom3d_frame} {s2 : geom3d_space f2}
    (tr: geom3d_transform s3 s2 ) : displacement3d s3 → displacement3d s2 :=
    λd,
    let as_pt : point s3 := ⟨λi, mk_pt real_scalar (d.coords i).coord⟩ in
    let tr_pt := (tr.to_equiv as_pt) in
    ⟨⟨λi, mk_vec real_scalar (tr_pt.coords i).coord⟩⟩


variables {f : geom3d_frame} (s : geom3d_space f )

structure orientation3d extends orientation s :=
mk ::

noncomputable instance o3i : inhabited (orientation3d s) := ⟨
    ⟨mk_orientation s (λi, mk_vectr s ⟨[0,0,0],rfl⟩)⟩
⟩

noncomputable def mk_orientation3d (s1 s2 s3 s4 s5 s6 s7 s8 s9 : real_scalar)--(ax1 : displacement3d s) (ax2 : displacement3d s) (ax3 : displacement3d s)
    : orientation3d s := ⟨mk_orientation s (λi, if i.1 = 0 then (mk_displacement3d s s1 s2 s3).to_vectr else if i.1 = 1 then (mk_displacement3d s s4 s5 s6).to_vectr else (mk_displacement3d s s7 s8 s9).to_vectr )⟩

    --: orientation3d s := ⟨mk_orientation s (λi, if i.1 = 0 then ax1.to_vectr else if i.1 = 1 then ax2.to_vectr else ax3.to_vectr )⟩


--okay, i can fill in this function now...
noncomputable def mk_orientation3d_from_euler_angles (s1 s2 s3 : real_scalar)--(ax1 : displacement3d s) (ax2 : displacement3d s) (ax3 : displacement3d s)
    : orientation3d s := ⟨mk_orientation s (λi, if i.1 = 0 then (mk_displacement3d s s1 s2 s3).to_vectr else if i.1 = 1 then (mk_displacement3d s s4 s5 s6).to_vectr else (mk_displacement3d s s7 s8 s9).to_vectr )⟩


noncomputable def mk_orientation3d_from_quaternion (s1 s2 s3 s4 : real_scalar)--(ax1 : displacement3d s) (ax2 : displacement3d s) (ax3 : displacement3d s)
    : orientation3d s := mk_orientation3d s 
        (2*(s1*s1 + s2*s2) - 1) (2*(s2*s3 - s1*s4)) (2*(s2*s4 + s1*s3))
        (2*(s2*s3 + s1*s4)) (2*(s1*s1 + s3*s3)) (2*(s3*s4 - s1*s2))
        (2*(s2*s4 - s1*s3)) (2*(s3*s4 + s1*s2)) (2*(s1*s1 + s1*s1 + s4*s4) - 1)
    --: orientation3d s := ⟨mk_orientation s (λi, if i.1 = 0 then ax1.to_vectr else if i.1 = 1 then ax2.to_vectr else ax3.to_vectr )⟩

noncomputable def geom3d_transform.transform_orientation
    {f3 : geom3d_frame} {s3 : geom3d_space f3}
    {f2 : geom3d_frame} {s2 : geom3d_space f2}
    (tr: geom3d_transform s3 s2 ) : orientation3d s3 → orientation3d s2 :=
    λo : orientation3d s3,
    ⟨tr.to_fm_tr.transform_orientation o.to_orientation⟩

structure rotation3d extends rotation s :=
mk ::

/-
noncomputable def mk_rotation3d (ax1 : displacement3d s) (ax2 : displacement3d s) (ax3 : displacement3d s)
    : rotation3d s := ⟨mk_rotation s (λi, if i.1 = 0 then ax1.to_vectr else if i.1 = 1 then ax2.to_vectr else ax3.to_vectr )⟩
-/
noncomputable def mk_rotation3d (s1 s2 s3 s4 s5 s6 s7 s8 s9 : real_scalar)--(ax1 : displacement3d s) (ax2 : displacement3d s) (ax3 : displacement3d s)
    : rotation3d s := ⟨mk_rotation s (λi, if i.1 = 0 then (mk_displacement3d s s1 s2 s3).to_vectr else if i.1 = 1 then (mk_displacement3d s s4 s5 s6).to_vectr else (mk_displacement3d s s7 s8 s9).to_vectr )⟩

noncomputable instance r3i : inhabited (rotation3d s) := ⟨
    mk_rotation3d s 1 1 1 1 1 1 1 1 1
⟩

noncomputable def mk_rotation3d_from_quaternion (s1 s2 s3 s4 : real_scalar)--(ax1 : displacement3d s) (ax2 : displacement3d s) (ax3 : displacement3d s)
    : rotation3d s := mk_rotation3d s 
        (2*(s1*s1 + s2*s2) - 1) (2*(s2*s3 - s1*s4)) (2*(s2*s4 + s1*s3))
        (2*(s2*s3 + s1*s4)) (2*(s1*s1 + s3*s3)) (2*(s3*s4 - s1*s2))
        (2*(s2*s4 - s1*s3)) (2*(s3*s4 + s1*s2)) (2*(s1*s1 + s1*s1 + s4*s4) - 1)
    --: orientation3d s := ⟨mk_orientation s (λi, if i.1 = 0 then ax1.to_vectr else if i.1 = 1 then ax2.to_vectr else ax3.to_vectr )⟩


structure pose3d :=
mk ::
    (orientation : orientation3d s)
    (position : position3d s)

def mk_pose3d (orientation : orientation3d s)
    (position : position3d s) : pose3d s := ⟨orientation,position⟩
 
 noncomputable instance p3i : inhabited (pose3d s) := ⟨
    (
    mk_pose3d _ 
    (mk_orientation3d _ 0 0 0 0 0 0 0 0 0)
    (mk_position3d _ 0 0 0)
    )
⟩


noncomputable def geom3d_transform.transform_pose3d
    {f3 : geom3d_frame} {s3 : geom3d_space f3}
    {f2 : geom3d_frame} {s2 : geom3d_space f2}
    (tr: geom3d_transform s3 s2 ) : pose3d s3 → pose3d s2 :=
    λp :_,
    (⟨tr.transform_orientation p.orientation, tr.transform_position3d p.position⟩:pose3d s2)
