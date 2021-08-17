import ..affnKcoord.affnKcoord_transforms
import data.real.basic
import linear_algebra.affine_space.basic
import topology.metric_space.emetric_space
import analysis.normed_space.inner_product
import data.complex.is_R_or_C
--import topology.metric_space.pi_Lp
import data.real.nnreal
import algebra.ordered_group
import analysis.special_functions.trigonometric

open_locale big_operators
open_locale nnreal

open ennreal

abbreviation K := ℝ

variables
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} (s : spc K f)
{dim2 : nat } {id_vec2 : fin dim → nat} {f2 : fm K dim id_vec} (s2 : spc K f2)



noncomputable def dot_product_coord
  : vectr s → vectr s → ℝ
| v1 v2 := 
    (∑ (i : fin dim), ↑((v1.coords i).coord * (v2.coords i).coord))
--amanda fill this in
noncomputable
instance : inner_product_space.core K (vectr s) := 
  ⟨dot_product_coord s,
  begin
    intros,
    simp only [is_R_or_C.conj_to_real, is_R_or_C.coe_real_eq_id, id.def],
    apply finset.sum_congr,
    refl,
    intros,
    apply mul_comm,
  end,
  begin
    intros,
    simp only [is_R_or_C.re_to_real, is_R_or_C.coe_real_eq_id, id.def],
    apply finset.sum_nonneg,
    intros,
    have neg_or_nonneg := classical.eq_false_or_eq_true ((x.coords i).coord ≥ 0),
    cases neg_or_nonneg,
    {
      simp only [not_le, eq_iff_iff, iff_false] at neg_or_nonneg,
      have neg_neg_pos := right.neg_pos_iff.2 neg_or_nonneg,
      have neg_mul_neg : (x.coords i).coord * (x.coords i).coord = -(x.coords i).coord * -(x.coords i).coord := 
        by simp only [neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg],
      rw neg_mul_neg,
      apply le_iff_lt_or_eq.2,
      apply or.inl,
      exact mul_pos neg_neg_pos neg_neg_pos,
    },
    {
      simp only [ge_iff_le, iff_true, eq_iff_iff] at neg_or_nonneg,
      have pos_or_zero := classical.eq_false_or_eq_true ((x.coords i).coord = 0),
      cases pos_or_zero,
      {
        simp only [eq_iff_iff, iff_false] at pos_or_zero,
        have pos : 0 < (x.coords i).coord := begin
          apply lt_of_le_of_ne,
          exact neg_or_nonneg,
          intro h,
          exact pos_or_zero (eq.symm h),
        end,
        apply le_iff_lt_or_eq.2,
        apply or.inl,
        exact mul_pos pos pos,
      },
      {
        simp only [iff_true, eq_iff_iff] at pos_or_zero,
        rw pos_or_zero,
        simp only [mul_zero],
      }
    }
  end,
  begin
    intros x h,
    simp only [is_R_or_C.coe_real_eq_id, id.def] at h,
    have h_nonneg : ∀ i : fin dim, i ∈ (@finset.univ (fin dim) _) → 0 ≤ (x.coords i).coord * (x.coords i).coord := begin
      intros,
      have neg_or_nonneg := classical.eq_false_or_eq_true ((x.coords i).coord ≥ 0),
      cases neg_or_nonneg,
      {
        simp only [not_le, eq_iff_iff, iff_false] at neg_or_nonneg,
        have neg_neg_pos := right.neg_pos_iff.2 neg_or_nonneg,
        have neg_mul_neg : (x.coords i).coord * (x.coords i).coord = -(x.coords i).coord * -(x.coords i).coord := 
          by simp only [neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg],
        rw neg_mul_neg,
        apply le_iff_lt_or_eq.2,
        apply or.inl,
        exact mul_pos neg_neg_pos neg_neg_pos,
      },
      {
        simp only [ge_iff_le, iff_true, eq_iff_iff] at neg_or_nonneg,
        have pos_or_zero := classical.eq_false_or_eq_true ((x.coords i).coord = 0),
        cases pos_or_zero,
        {
          simp only [eq_iff_iff, iff_false] at pos_or_zero,
          have pos : 0 < (x.coords i).coord := begin
            apply lt_of_le_of_ne,
            exact neg_or_nonneg,
            intro h,
            exact pos_or_zero (eq.symm h),
          end,
          apply le_iff_lt_or_eq.2,
          apply or.inl,
          exact mul_pos pos pos,
        },
        {
          simp only [iff_true, eq_iff_iff] at pos_or_zero,
          rw pos_or_zero,
          simp only [mul_zero],
        }
      }
    end,
    have h₀ := (finset.sum_eq_zero_iff_of_nonneg h_nonneg).1 h,
    ext,
    dsimp only [has_zero.zero],
    dsimp only [add_zero_class.zero, add_monoid.zero, sub_neg_monoid.zero, add_group.zero, add_comm_group.zero, vectr_zero, mk_vectr, mk_vec_n, mk_vec, vector.nth],
    simp only [list.nth_le_repeat],
    have x_1_in_univ : x_1 ∈ (@finset.univ (fin dim) _) := by simp only [finset.mem_univ],
    have mul_self_zero := h₀ x_1 x_1_in_univ,
    have mul_self_nonneg : (x.coords x_1).coord * (x.coords x_1).coord ≤ 0 := le_iff_lt_or_eq.2 (or.inr mul_self_zero),
    have sqrt_mul_self_nonneg := real.sqrt_eq_zero'.2 mul_self_nonneg,
    simp only [real.sqrt_mul_self_eq_abs] at sqrt_mul_self_nonneg,
    exact abs_eq_zero.1 sqrt_mul_self_nonneg,
  end,
  begin
    intros,
    simp only [is_R_or_C.coe_real_eq_id, id.def],
    have h := @finset.sum_add_distrib K (fin dim) finset.univ (λ i : fin dim, (x.coords i).coord * (z.coords i).coord) (λ i : fin dim, (y.coords i).coord * (z.coords i).coord) _,
    simp only at h,
    rw eq.symm h,
    apply finset.sum_congr,
    refl,
    intros,
    have add_is : ((x + y).coords x_1).coord = (x.coords x_1).coord + (y.coords x_1).coord := begin
      dsimp only [has_add.add],
      refl,
    end,
    rw add_is,
    exact distrib.right_distrib (x.coords x_1).coord (y.coords x_1).coord (z.coords x_1).coord,
  end,
  begin
    intros,
    simp only [is_R_or_C.conj_to_real, is_R_or_C.coe_real_eq_id, id.def],
    dsimp only [has_scalar.smul],
    dsimp only [smul_vectr, has_scalar.smul],
    dsimp only [smul_vec, mk_vectr'],
    simp only [mul_assoc],
    apply eq.symm finset.mul_sum,
  end⟩

  
open inner_product_space.of_core

noncomputable instance vectr_inner : has_inner ℝ (vectr s) := ⟨dot_product_coord s⟩
notation `⟪`x`, `y`⟫` := has_inner.inner x y

noncomputable
instance : has_norm (vectr s ) := (@inner_product_space.of_core.to_has_norm K (vectr s) _ _ _ _)

noncomputable def norm_coord
  : vectr s → ℝ
| v1 := 
    real.sqrt ((@is_R_or_C.re K _) ⟪v1, v1⟫)

noncomputable instance vectr_norm : has_norm (vectr s) :=
{ norm := λ x, real.sqrt ((@is_R_or_C.re K _) ⟪x, x⟫) }


noncomputable
def l2_metric
  : point s → point s → ℝ
| pt1 pt2 := ∥pt1 -ᵥ pt2∥

noncomputable
def l2_extended_metric
  : point s → point s → ennreal
| pt1 pt2 := option.some (⟨∥pt1 -ᵥ pt2∥,begin
  dsimp only [has_norm.norm],
  apply real.sqrt_nonneg,
  admit
end⟩:(ℝ≥0))

noncomputable
instance euclidean_distance_coord : has_dist (point s) := ⟨l2_metric s⟩ 

noncomputable
instance euclidean_extended_distance_coord : has_edist (point s) := ⟨l2_extended_metric s⟩

/-
structure emetric_space (α : Type u) :
Type u
to_has_edist : has_edist α
edist_self : ∀ (x : α), edist x x = 0
eq_of_edist_eq_zero : ∀ {x y : α}, edist x y = 0 → x = y
edist_comm : ∀ (x y : α), edist x y = edist y x
edist_triangle : ∀ (x y z : α), edist x z ≤ edist x y + edist y z
to_uniform_space : uniform_space α
uniformity_edist : (𝓤 α = ⨅ (ε : ennreal) (H : ε > 0), 𝓟 {p : α × α | edist p.fst p.snd < ε}) . "control_laws_tac"
-/
/-
class metric_space (α : Type u) extends has_dist α : Type u :=
(dist_self : ∀ x : α, dist x x = 0)
(eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y)
(dist_comm : ∀ x y : α, dist x y = dist y x)
(dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
(edist : α → α → ennreal := λx y, ennreal.of_real (dist x y))
(edist_dist : ∀ x y : α, edist x y = ennreal.of_real (dist x y) . control_laws_tac)
(to_uniform_space : uniform_space α := uniform_space_of_dist dist dist_self dist_comm dist_triangle)
(uniformity_dist : 𝓤 α = ⨅ ε>0, 𝓟 {p:α×α | dist p.1 p.2 < ε} . control_laws_tac)


-/
/-


-/
--#eval noncomputable_value -- doesn't work


noncomputable instance euclidean_pseudo_metric_space_pt : pseudo_metric_space (point s)
  := ⟨begin
    intros,
    dsimp only [dist, l2_metric, norm, norm_coord, dot_product_coord,
      has_vsub.vsub, aff_point_group_sub, sub_point_point, 
      mk_vectr', aff_pt_group_sub, sub_pt_pt],
    simp,
  end, begin
    intros,
    dsimp only [dist, l2_metric, norm, norm_coord, dot_product_coord, 
      has_vsub.vsub, aff_point_group_sub, sub_point_point, 
      mk_vectr', aff_pt_group_sub, sub_pt_pt],
    suffices h :(∑ (i : fin dim), ↑(((x.coords i).coord - (y.coords i).coord) * ((x.coords i).coord - (y.coords i).coord))) = (∑ (i : fin dim), ↑(((y.coords i).coord - (x.coords i).coord) * ((y.coords i).coord - (x.coords i).coord))),
    rw h,
    apply finset.sum_congr,
    refl,
    intros x_1 h,
    simp only [is_R_or_C.coe_real_eq_id, id.def],
    have h₀ : ((x.coords x_1).coord - (y.coords x_1).coord) = -((y.coords x_1).coord - (x.coords x_1).coord) := by simp only [neg_sub],
    rw h₀,
    simp only [neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg],
  end, begin
    intros,
    dsimp only [dist, l2_metric],
    have cauchy_schwarz : ∀ p q : vectr s, ∥dot_product_coord s p q∥ ≤ ∥p∥ * ∥q∥ := begin
      intros,
      have h := real_inner_mul_inner_self_le p q,
      dsimp only [is_R_or_C.abs, is_R_or_C.norm_sq] at h,
      simp only [is_R_or_C.re_to_real, add_zero, monoid_with_zero_hom.coe_mk, is_R_or_C.im_to_real, mul_zero] at h,
      --dsimp only [has_inner.inner] at h,
      have square_norm_nonneg : ∀ c : ℝ, ∥p +ᵥ (-c)•q∥^2 ≥ 0 := begin
        intros,
        rw sq,
        dsimp only [has_norm.norm, norm_coord],
        have nonpos_or_pos := classical.eq_false_or_eq_true (dot_product_coord s (p +ᵥ -c • q) (p +ᵥ -c • q) > 0),
        cases nonpos_or_pos,
        {
          simp only [not_lt, eq_iff_iff, iff_false] at nonpos_or_pos,
          rw real.sqrt_eq_zero_of_nonpos nonpos_or_pos,
          simp only [ge_iff_le, mul_zero],
        },
        {
          simp only [gt_iff_lt, iff_true, eq_iff_iff] at nonpos_or_pos,
          have sqrt_pos := real.sqrt_pos.2 nonpos_or_pos,
          have mul_sqrt_pos := mul_pos sqrt_pos sqrt_pos,
          simp only [ge_iff_le],
          apply le_iff_lt_or_eq.2,
          apply or.inl,
          exact mul_sqrt_pos,
        },
      end,
      have h₀ : ∀ c : ℝ, ∥p +ᵥ (-c)•q∥^2 = ∥q∥^2*c^2 - 2*c*(dot_product_coord s p q) + ∥p∥^2 := sorry,
      have h₁ : ∀ c : ℝ, ∥q∥^2*c^2 - 2*c*(dot_product_coord s p q) + ∥p∥^2 ≥ 0 := begin
        intros,
        rw eq.symm (h₀ c),
        exact square_norm_nonneg c,
      end,
      have discriminant_nonpos : -2*(dot_product_coord s p q) * -2*(dot_product_coord s p q) - 4 * ∥p∥*∥p∥*∥q∥*∥q∥ ≤ 0 := sorry,
      have h₂ : (-2) * dot_product_coord s p q * -2 * dot_product_coord s p q = 4 * dot_product_coord s p q * dot_product_coord s p q := begin
        simp only [neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg, mul_eq_mul_right_iff],
        apply or.inl,
        rw mul_comm,
        rw eq.symm (mul_assoc _ _ _),
        simp only [mul_eq_mul_right_iff],
        apply or.inl,
        rw two_mul (2 : ℝ),
        refl,
      end,
      have h₃ : 0 = 4 * ∥p∥ * ∥p∥ * ∥q∥ * ∥q∥ - 4 * ∥p∥ * ∥p∥ * ∥q∥ * ∥q∥ := by simp,
      rw [h₂, h₃] at discriminant_nonpos,
      have h₄ :  4 * dot_product_coord s p q * dot_product_coord s p q ≤ 4 * ∥p∥*∥p∥*∥q∥*∥q∥ :=
        (sub_le_sub_iff_right (4 * ∥p∥ * ∥p∥ * ∥q∥ * ∥q∥)).1 discriminant_nonpos,
      /-have h₅ : (0:ℝ) ≤ (4:ℝ) := by simp only [zero_le_one, zero_le_bit0],
      have h₆ := div_le_div_of_le h₅ h₄,
      have h₇ : 4 * dot_product_coord s p q * dot_product_coord s p q = dot_product_coord s p q * dot_product_coord s p q * 4 := begin
        have hy : 4 * dot_product_coord s p q * dot_product_coord s p q = 4 * (dot_product_coord s p q * dot_product_coord s p q) :=
          by exact mul_assoc 4 (dot_product_coord s p q) (dot_product_coord s p q),
        rw hy,
        exact mul_comm 4 (dot_product_coord s p q * dot_product_coord s p q),
      end,-/
      /-have h₅ : (0:ℝ) < 4⁻¹ := by simp,
      have h₆ : (4:ℝ) = ((4:ℝ)⁻¹)⁻¹ := by simp only [inv_inv'],
      rw h₆ at h₄,
      have h₇ := (inv_mul_le_iff h₅).1 h₄,-/
      repeat {sorry},
    end,
    have abs_add_le_add_abs : ∀ p q : vectr s, ∥p +ᵥ q∥ ≤ ∥p∥ + ∥q∥ := sorry,
    have h₀ : x -ᵥ z = x -ᵥ y +ᵥ (y -ᵥ z) := begin
      have hy : x -ᵥ y +ᵥ (y -ᵥ z) = (x -ᵥ y +ᵥ y) -ᵥ z := begin
        simp,
        simp only [point_vsub_vadd_a1],
        sorry,
      end,
      rw hy,
      rw point_vsub_vadd_a1 s x y,
    end,
    rw h₀,
    exact abs_add_le_add_abs (x -ᵥ y) (y -ᵥ z),
  end, sorry, sorry, sorry, sorry⟩

/-instance euclidean_dist_vec : has_dist (vectr s)
  := ⟨sorry⟩-/

/-instance euclidean_pseudo_metric_space_vec : pseudo_metric_space (vectr s)
  := ⟨sorry, sorry, sorry, sorry, sorry, sorry, sorry⟩-/

noncomputable
instance euclidean_metric_space_pt : metric_space (point s)
  := ⟨begin
    intros x y h,
    dsimp only [dist, l2_metric, norm, norm_coord, dot_product_coord, 
      has_vsub.vsub, aff_point_group_sub, sub_point_point, 
      mk_vectr', aff_pt_group_sub, sub_pt_pt] at h,
    have sum_nonpos := real.sqrt_eq_zero'.1 h,
    have mul_self_nonneg : ∀ r : ℝ, r * r ≥ 0 := begin
      intros,
      have nonneg_or_neg := classical.eq_false_or_eq_true (r ≥ 0),
      cases nonneg_or_neg,
      {
        have r_neg : ¬(r ≥ 0) := begin
          rw nonneg_or_neg,
          simp only [not_false_iff],
        end,
        simp only [not_le] at r_neg,
        have neg_r_pos : 0 < -r := begin
          have zero_neg : (0:ℝ) = -0 := by simp only [neg_zero],
          rw zero_neg,
          exact neg_lt_neg_iff.2 r_neg,
        end,
        have mul_neg_neg : r * r = (-r) * (-r) := by simp only [neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg],
        rw mul_neg_neg,
        have mul_neg_neg_nonneg : 0 < -r * -r ∨ 0 = -r * -r := or.inl (mul_pos neg_r_pos neg_r_pos),
        exact le_iff_lt_or_eq.2 mul_neg_neg_nonneg,
      },
      {
        have nonneg : r ≥ 0 := begin
          rw nonneg_or_neg,
          apply true.intro,
        end,
        cases (lt_or_eq_of_le nonneg),
        {
          have lt_or_eq : 0 < r * r ∨ 0 = r * r := or.inl (mul_pos h_1 h_1),
          simp only [ge_iff_le],
          exact le_iff_lt_or_eq.2 lt_or_eq,
        },
        {
          rw (eq.symm h_1),
          simp only [ge_iff_le, mul_zero],
        },
      },
    end,
    have sum_nonneg : ∑ (i : fin dim), (↑(((x.coords i).coord - (y.coords i).coord) * ((x.coords i).coord - (y.coords i).coord)) : ℝ) ≥ 0 := begin
      simp only [is_R_or_C.coe_real_eq_id, id.def],
      apply finset.sum_nonneg,
      intros,
      apply mul_self_nonneg,
    end,
    have sum_zero : ∑ (i : fin dim), (↑(((x.coords i).coord - (y.coords i).coord) * ((x.coords i).coord - (y.coords i).coord)) : ℝ) = 0 := le_antisymm sum_nonpos sum_nonneg,
    simp only [is_R_or_C.coe_real_eq_id, id.def] at sum_zero,
    have f : fin dim → ℝ := λ i, ((x.coords i).coord - (y.coords i).coord) * ((x.coords i).coord - (y.coords i).coord),
    have h₀ : ∀ i ∈ (@finset.univ (fin dim) _), 0 ≤ ((x.coords i).coord - (y.coords i).coord) * ((x.coords i).coord - (y.coords i).coord) := begin
      intros,
      apply mul_self_nonneg,
    end,
    ext,
    have in_univ : x_1 ∈ (@finset.univ (fin dim) _) := by simp only [finset.mem_univ],
    have h₁ := (finset.sum_eq_zero_iff_of_nonneg h₀).1 sum_zero x_1 in_univ,
    have le_zero : ((x.coords x_1).coord - (y.coords x_1).coord) * ((x.coords x_1).coord - (y.coords x_1).coord) ≤ 0 := begin
      apply le_iff_lt_or_eq.2,
      apply or.inr,
      exact h₁,
    end,
    have sqrt_zero := real.sqrt_eq_zero'.2 le_zero,
    rw real.sqrt_mul_self_eq_abs at sqrt_zero,
    have h₂ := abs_eq_zero.1 sqrt_zero,
    have zero_is : 0 = -(y.coords x_1).coord + (y.coords x_1).coord := by simp only [add_left_neg],
    rw [sub_eq_add_neg, add_comm, zero_is] at h₂,
    exact add_left_cancel h₂,
  end⟩

/-instance euclidean_metric_space_vec : metric_space (vectr s)
  := ⟨begin
    intros x y h,
    sorry,
  end⟩-/

noncomputable
instance euclidean_pseudo_extended_metric_space_pt : pseudo_emetric_space (point s) 
  := ⟨begin
    intros,
    dsimp only [edist, l2_extended_metric],
    simp only [some_eq_coe, coe_eq_zero],
    dsimp only [has_zero.zero],
    simp only [subtype.mk_eq_mk],
    dsimp only [has_norm.norm, norm_coord, dot_product_coord],
    simp only [is_R_or_C.coe_real_eq_id, id.def],
    dsimp only [has_vsub.vsub, aff_point_group_sub, sub_point_point, aff_pt_group_sub, sub_pt_pt, mk_vectr'],
    simp,
    refl,
  end, begin
    intros,
    dsimp only [edist, l2_extended_metric, norm, norm_coord, dot_product_coord, has_vsub.vsub],
    dsimp only [aff_point_group_sub, sub_point_point, has_vsub.vsub],
    dsimp only [aff_pt_group_sub, sub_pt_pt, mk_vectr'],
    simp only [is_R_or_C.coe_real_eq_id, coe_eq_coe, id.def, subtype.mk_eq_mk, some_eq_coe],
    suffices h : (∑ (i : fin dim), ((x.coords i).coord - (y.coords i).coord) * ((x.coords i).coord - (y.coords i).coord)) = (∑ (i : fin dim), ((y.coords i).coord - (x.coords i).coord) * ((y.coords i).coord - (x.coords i).coord)),
    rw h,
    apply finset.sum_congr,
    refl,
    intros,
    have neg_sub : ((y.coords x_1).coord - (x.coords x_1).coord) = -((x.coords x_1).coord - (y.coords x_1).coord) := by simp only [neg_sub],
    rw neg_sub,
    exact eq.symm (neg_mul_neg ((x.coords x_1).coord - (y.coords x_1).coord) ((x.coords x_1).coord - (y.coords x_1).coord)),
  end, begin
    intros,
    dsimp only [edist, l2_extended_metric],
    simp only [some_eq_coe],
    -- should be similar to the above triangle proof at line 98
    sorry,
  end, sorry, sorry⟩

/-instance euclidean_pseudo_extended_metric_space_vec : pseudo_emetric_space (vectr s)
  := ⟨sorry, sorry, sorry, sorry, sorry⟩-/

noncomputable
instance euclidean_extended_metric_space_pt : emetric_space (point s) 
  := ⟨begin
    intros x y h,
    dsimp only [edist, l2_extended_metric] at h,
    simp only [some_eq_coe, coe_eq_zero] at h,
    dsimp only [has_zero.zero] at h,
    simp only [subtype.mk_eq_mk] at h,
    dsimp only [has_norm.norm, norm_coord, dot_product_coord] at h,
    simp only [is_R_or_C.coe_real_eq_id, id.def] at h,
    have sum_nonpos := real.sqrt_eq_zero'.1 h,
    
    have mul_self_nonneg : ∀ r : ℝ, r * r ≥ 0 := begin
      intros,
      have nonneg_or_neg := classical.eq_false_or_eq_true (r ≥ 0),
      cases nonneg_or_neg,
      {
        have r_neg : ¬(r ≥ 0) := begin
          rw nonneg_or_neg,
          simp only [not_false_iff],
        end,
        simp only [not_le] at r_neg,
        have neg_r_pos : 0 < -r := begin
          have zero_neg : (0:ℝ) = -0 := by simp only [neg_zero],
          rw zero_neg,
          exact neg_lt_neg_iff.2 r_neg,
        end,
        have mul_neg_neg : r * r = (-r) * (-r) := by simp only [neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg],
        rw mul_neg_neg,
        have mul_neg_neg_nonneg : 0 < -r * -r ∨ 0 = -r * -r := or.inl (mul_pos neg_r_pos neg_r_pos),
        exact le_iff_lt_or_eq.2 mul_neg_neg_nonneg,
      },
      {
        have nonneg : r ≥ 0 := begin
          rw nonneg_or_neg,
          apply true.intro,
        end,
        cases (lt_or_eq_of_le nonneg),
        {
          have lt_or_eq : 0 < r * r ∨ 0 = r * r := or.inl (mul_pos h_1 h_1),
          simp only [ge_iff_le],
          exact le_iff_lt_or_eq.2 lt_or_eq,
        },
        {
          rw (eq.symm h_1),
          simp only [ge_iff_le, mul_zero],
        },
      },
    end,
    have sum_nonneg : ∑ (i : fin dim), (↑(((x.coords i).coord - (y.coords i).coord) * ((x.coords i).coord - (y.coords i).coord)) : ℝ) ≥ 0 := begin
      simp only [is_R_or_C.coe_real_eq_id, id.def],
      apply finset.sum_nonneg,
      intros,
      apply mul_self_nonneg,
    end,
    have sum_zero : ∑ (i : fin dim), (↑(((x.coords i).coord - (y.coords i).coord) * ((x.coords i).coord - (y.coords i).coord)) : ℝ) = 0 := le_antisymm sum_nonpos sum_nonneg,
    simp only [is_R_or_C.coe_real_eq_id, id.def] at sum_zero,
    have f : fin dim → ℝ := λ i, ((x.coords i).coord - (y.coords i).coord) * ((x.coords i).coord - (y.coords i).coord),
    have h₀ : ∀ i ∈ (@finset.univ (fin dim) _), 0 ≤ ((x.coords i).coord - (y.coords i).coord) * ((x.coords i).coord - (y.coords i).coord) := begin
      intros,
      apply mul_self_nonneg,
    end,
    ext,
    have in_univ : x_1 ∈ (@finset.univ (fin dim) _) := by simp only [finset.mem_univ],
    have h₁ := (finset.sum_eq_zero_iff_of_nonneg h₀).1 sum_zero x_1 in_univ,
    have le_zero : ((x.coords x_1).coord - (y.coords x_1).coord) * ((x.coords x_1).coord - (y.coords x_1).coord) ≤ 0 := begin
      apply le_iff_lt_or_eq.2,
      apply or.inr,
      exact h₁,
    end,
    have sqrt_zero := real.sqrt_eq_zero'.2 le_zero,
    rw real.sqrt_mul_self_eq_abs at sqrt_zero,
    have h₂ := abs_eq_zero.1 sqrt_zero,
    have zero_is : 0 = -(y.coords x_1).coord + (y.coords x_1).coord := by simp only [add_left_neg],
    rw [sub_eq_add_neg, add_comm, zero_is] at h₂,
    exact add_left_cancel h₂,
  end⟩

/-noncomputable
instance euclidean_extended_metric_space_vec : emetric_space (vectr s) 
  := ⟨sorry⟩-/


noncomputable
instance euclidean_extended_metric_space : emetric_space (point s) 
  := ⟨begin
    intros x y h,
    dsimp only [edist, l2_extended_metric] at h,
    simp only [some_eq_coe, coe_eq_zero] at h,
    dsimp only [has_zero.zero] at h,
    simp only [subtype.mk_eq_mk] at h,
    simp only [has_norm.norm, norm_coord, dot_product_coord, 
      is_R_or_C.coe_real_eq_id, id.def, has_vsub.vsub,
      aff_point_group_sub, sub_point_point, aff_pt_group_sub,
      sub_pt_pt, mk_vectr'] at h,
    have sum_nonpos := real.sqrt_eq_zero'.1 h,
    have mul_self_nonneg : ∀ r : ℝ, r * r ≥ 0 := begin
      intros,
      have nonneg_or_neg := classical.eq_false_or_eq_true (r ≥ 0),
      cases nonneg_or_neg,
      {
        have r_neg : ¬(r ≥ 0) := begin
          rw nonneg_or_neg,
          simp only [not_false_iff],
        end,
        simp only [not_le] at r_neg,
        have neg_r_pos : 0 < -r := begin
          have zero_neg : (0:ℝ) = -0 := by simp only [neg_zero],
          rw zero_neg,
          exact neg_lt_neg_iff.2 r_neg,
        end,
        have mul_neg_neg : r * r = (-r) * (-r) := by simp only [neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg],
        rw mul_neg_neg,
        have mul_neg_neg_nonneg : 0 < -r * -r ∨ 0 = -r * -r := or.inl (mul_pos neg_r_pos neg_r_pos),
        exact le_iff_lt_or_eq.2 mul_neg_neg_nonneg,
      },
      {
        have nonneg : r ≥ 0 := begin
          rw nonneg_or_neg,
          apply true.intro,
        end,
        cases (lt_or_eq_of_le nonneg),
        {
          have lt_or_eq : 0 < r * r ∨ 0 = r * r := or.inl (mul_pos h_1 h_1),
          simp only [ge_iff_le],
          exact le_iff_lt_or_eq.2 lt_or_eq,
        },
        {
          rw (eq.symm h_1),
          simp only [ge_iff_le, mul_zero],
        },
      },
    end,
    have sum_nonneg : ∑ (i : fin dim), (↑(((x.coords i).coord - (y.coords i).coord) * ((x.coords i).coord - (y.coords i).coord)) : ℝ) ≥ 0 := begin
      simp only [is_R_or_C.coe_real_eq_id, id.def],
      apply finset.sum_nonneg,
      intros,
      apply mul_self_nonneg,
    end,
    have sum_zero : ∑ (i : fin dim), (↑(((x.coords i).coord - (y.coords i).coord) * ((x.coords i).coord - (y.coords i).coord)) : ℝ) = 0 := le_antisymm sum_nonpos sum_nonneg,
    simp only [is_R_or_C.coe_real_eq_id, id.def] at sum_zero,
    have f : fin dim → ℝ := λ i, ((x.coords i).coord - (y.coords i).coord) * ((x.coords i).coord - (y.coords i).coord),
    have h₀ : ∀ i ∈ (@finset.univ (fin dim) _), 0 ≤ ((x.coords i).coord - (y.coords i).coord) * ((x.coords i).coord - (y.coords i).coord) := begin
      intros,
      apply mul_self_nonneg,
    end,
    ext,
    have in_univ : x_1 ∈ (@finset.univ (fin dim) _) := by simp only [finset.mem_univ],
    have h₁ := (finset.sum_eq_zero_iff_of_nonneg h₀).1 sum_zero x_1 in_univ,
    have le_zero : ((x.coords x_1).coord - (y.coords x_1).coord) * ((x.coords x_1).coord - (y.coords x_1).coord) ≤ 0 := begin
      apply le_iff_lt_or_eq.2,
      apply or.inr,
      exact h₁,
    end,
    have sqrt_zero := real.sqrt_eq_zero'.2 le_zero,
    rw real.sqrt_mul_self_eq_abs at sqrt_zero,
    have h₂ := abs_eq_zero.1 sqrt_zero,
    have zero_is : 0 = -(y.coords x_1).coord + (y.coords x_1).coord := by simp only [add_left_neg],
    rw [sub_eq_add_neg, add_comm, zero_is] at h₂,
    exact add_left_cancel h₂,
  end⟩
   
/-
(dist_eq : ∀ x y, dist x y = norm (x - y))
-/

noncomputable 
instance euclidean_normed_group : normed_group (vectr s) 
  :=
  ⟨
    begin
      intros,
      dsimp only [has_norm.norm, norm_coord, dot_product_coord],
      dsimp only [dist],
      sorry
    end
  ⟩
/-
(norm_smul_le : ∀ (a:α) (b:β), ∥a • b∥ ≤ ∥a∥ * ∥b∥)
-/

/-noncomputable 
instance euclidean_normed_space [module K (vectr s)] : normed_space K (vectr s) 
  :=
  ⟨begin
    intros,
    dsimp only [has_norm.norm, norm_coord, dot_product_coord],
    simp only [is_R_or_C.coe_real_eq_id, id.def],
    rw eq.symm (real.sqrt_mul_self (abs_nonneg a)),
    have sqrt_mul : ∀ x y : ℝ, real.sqrt x * real.sqrt y = real.sqrt (x*y) := begin
      intros,
      sorry,
    end,
    have mul_abs : abs a * abs a = a * a := begin
      cases (abs_choice a),
      repeat {rw h},
      simp only [neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg],
    end,
    have sqrt_le_sqrt : ∀ x y : ℝ,  x ≤ y → real.sqrt x ≤ real.sqrt y := begin
      intros x y h,
      sorry,
    end,
    rw [sqrt_mul, mul_abs],
    apply sqrt_le_sqrt,
    have const_distrib : ∀ c : ℝ, ∀ f : fin dim → ℝ, c * ∑ (i : fin dim), f i = ∑ (i : fin dim), c * f i := sorry,
    have f : fin dim → ℝ := λ i, (b.coords i).coord * (b.coords i).coord,
    -- apply const_distrib (a * a) f,
    sorry,
  end⟩-/

/-
class inner_product_space (𝕜 : Type*) (E : Type*) [is_R_or_C 𝕜]
  extends normed_group E, normed_space 𝕜 E, has_inner 𝕜 E :=
(norm_sq_eq_inner : ∀ (x : E), ∥x∥^2 = re (inner x x))
(conj_sym  : ∀ x y, conj (inner y x) = inner x y)
(nonneg_im : ∀ x, im (inner x x) = 0)
(add_left  : ∀ x y z, inner (x + y) z = inner x z + inner y z)
(smul_left : ∀ x y r, inner (r • x) y = (conj r) * inner x y)

-/

/-noncomputable
instance euclidean_normed_space_vec : normedw_space ℝ (vectr s)
  := ⟨begin
    intros,
    dsimp only [has_norm.norm, norm_coord, dot_product_coord, 
      has_scalar.smul, smul_vectr, smul_vec, mk_vectr'],
    rw eq.symm (real.sqrt_mul_self_eq_abs a),
    have h₀ : (∑ (i : fin dim), ↑(a * (b.coords i).coord * (a * (b.coords i).coord))) = (∑ (i : fin dim), ↑(a * a * (b.coords i).coord * (b.coords i).coord)) := sorry,
    have h₁ : (∑ (i : fin dim), ↑(a * a * (b.coords i).coord * (b.coords i).coord)) = a * a * (∑ (i : fin dim), ↑((b.coords i).coord * (b.coords i).coord)) := sorry,
    have h₂ : ∀ x y : ℝ, real.sqrt x * real.sqrt y = real.sqrt (x * y) := sorry,
    rw [h₀, h₁, h₂],
  end⟩-/

noncomputable
instance euclidean_inner_product_space : inner_product_space ℝ (vectr s)
  := ⟨begin
    intros,
    dsimp only [has_norm.norm, norm_coord, is_R_or_C.re, has_inner.inner, dot_product_coord],
    simp only [is_R_or_C.coe_real_eq_id, id.def, add_monoid_hom.id_apply],
    apply real.sq_sqrt,
    apply finset.sum_nonneg,
    intros,
    have mul_self_nonneg : ∀ r : ℝ, r * r ≥ 0 := begin
      intros,
      have nonneg_or_neg := classical.eq_false_or_eq_true (r ≥ 0),
      cases nonneg_or_neg,
      {
        have r_neg : ¬(r ≥ 0) := begin
          rw nonneg_or_neg,
          simp only [not_false_iff],
        end,
        simp only [not_le] at r_neg,
        have neg_r_pos : 0 < -r := begin
          have zero_neg : (0:ℝ) = -0 := by simp only [neg_zero],
          rw zero_neg,
          exact neg_lt_neg_iff.2 r_neg,
        end,
        have mul_neg_neg : r * r = (-r) * (-r) := by simp only [neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg],
        rw mul_neg_neg,
        have mul_neg_neg_nonneg : 0 < -r * -r ∨ 0 = -r * -r := or.inl (mul_pos neg_r_pos neg_r_pos),
        exact le_iff_lt_or_eq.2 mul_neg_neg_nonneg,
      },
      {
        have nonneg : r ≥ 0 := begin
          rw nonneg_or_neg,
          apply true.intro,
        end,
        cases (lt_or_eq_of_le nonneg),
        {
          have lt_or_eq : 0 < r * r ∨ 0 = r * r := or.inl (mul_pos h h),
          simp only [ge_iff_le],
          exact le_iff_lt_or_eq.2 lt_or_eq,
        },
        {
          rw (eq.symm h),
          simp only [ge_iff_le, mul_zero],
        },
      },
    end,
    exact mul_self_nonneg (x.coords i).coord,
  end, begin
    intros,
    dsimp only [is_R_or_C.conj, has_inner.inner, dot_product_coord],
    simp only [is_R_or_C.coe_real_eq_id, id.def, ring_hom.id_apply],
    apply finset.sum_congr,
    refl,
    intros,
    sorry,
    -- can't prove this unless x = y
  end, begin
    intros,
    dsimp only [has_inner.inner, dot_product_coord, has_add.add],
    dsimp only [add_zero_class.add, add_monoid.add, add_vectr_vectr, has_add.add],
    dsimp only [sub_neg_monoid.add, add_group.add, add_comm_group.add, add_monoid.add, add_vectr_vectr, has_add.add],
    dsimp only [add_vec_vec, mk_vectr'],
    simp only [is_R_or_C.coe_real_eq_id, id.def],
    have distrib_add_is : distrib.add (∑ (i : fin dim), (x.coords i).coord * (x.coords i).coord) (∑ (i : fin dim), (y.coords i).coord * (y.coords i).coord) = (∑ (i : fin dim), (x.coords i).coord * (x.coords i).coord) + (∑ (i : fin dim), (y.coords i).coord * (y.coords i).coord) := rfl,
    have sum_add_distrib : ∑ (i : fin dim), (x.coords i).coord * (x.coords i).coord + ∑ (i : fin dim), (y.coords i).coord * (y.coords i).coord = ∑ (i : fin dim), ((x.coords i).coord * (x.coords i).coord + (y.coords i).coord * (y.coords i).coord) := begin
      symmetry,
      apply finset.sum_add_distrib,
    end,
    rw [distrib_add_is, sum_add_distrib],
    apply finset.sum_congr,
    refl,
    intros,
    sorry,
    -- can't prove this unless 2xy = 0
  end, begin
    intros,
    dsimp only [has_inner.inner, dot_product_coord, is_R_or_C.conj, has_scalar.smul],
    dsimp only [smul_vectr, has_scalar.smul],
    dsimp only [smul_vec, mk_vectr'],
    simp only [is_R_or_C.coe_real_eq_id, id.def, ring_hom.id_apply],
    have const_distrib : r * ∑ (i : fin dim), (x.coords i).coord * (x.coords i).coord = ∑ (i : fin dim), r * ((x.coords i).coord * (x.coords i).coord) := sorry,
    rw const_distrib,
    apply finset.sum_congr,
    refl,
    intros,
    sorry,
    -- can't prove this unless r = 0 or r = 1
  end⟩



structure affine_euclidean_space.angle 
  :=
  (val : ℝ)



noncomputable
def vectr.compute_angle
    (v1 : vectr s)
    : vectr s → affine_euclidean_space.angle
    := 
      λ v2,
      ⟨real.arccos ⟪v1,v2⟫/∥v1∥*∥v2∥⟩


structure orientation extends vectr_basis s := 
    (col_norm_one : ∀ i : fin dim, ∥basis_vectrs i∥ = 1)
    (col_orthogonal : ∀ i j : fin dim, i≠j → ⟪basis_vectrs i,basis_vectrs j⟫ = (0:ℝ))

/-
don't prove here *yet*
-/
noncomputable
def mk_orientation (ortho_vectrs : fin dim → vectr s) : orientation s :=
  ⟨⟨ortho_vectrs, sorry, sorry⟩, begin
    intros,
    simp only,
    dsimp only [has_norm.norm, norm_coord, dot_product_coord],
    have h₁ : ∀ r : ℝ, real.sqrt r = 1 ↔ r = 1 := λ r,
      if nonneg : 0 ≤ r then begin
        intros,
        split,
        intro h,
        have h₂ : (0 : ℝ) ≤ (1 : ℝ) := begin
          have h₃ : (0 : ℝ) < 1 ∨ (0 : ℝ) = 1 := or.inl real.zero_lt_one,
          have h₄ := le_iff_lt_or_eq.2 h₃,
          exact h₄,
        end,
        have h₃ := (real.sqrt_eq_iff_mul_self_eq nonneg h₂).1 h,
        simp only [mul_one] at h₃,
        exact eq.symm h₃,
        intro h,
        rw h,
        exact real.sqrt_one,
      end
      else begin
        simp only [not_le] at nonneg,
        have h₂ : r ≤ 0 := begin
          have h₃ : r < 0 ∨ r = 0 := or.inl nonneg,
          have h₄ := le_iff_lt_or_eq.2 h₃,
          exact h₄,
        end,
        intros,
        split,
        intro h,
        have h₃ := eq.trans (eq.symm (real.sqrt_eq_zero_of_nonpos h₂)) h,
        have h₄ := zero_ne_one h₃,
        contradiction,
        intro h,
        rw h at nonneg,
        have h₃ := lt_asymm real.zero_lt_one,
        contradiction,
      end,
    rw h₁,
    sorry,
    -- no idea how to approach this one
  end, begin
    intros i j h,
    simp only,
    dsimp only [has_inner.inner, dot_product_coord],
    simp only [is_R_or_C.coe_real_eq_id, id.def],
    sorry,
    -- no idea what to do here, either
  end⟩

structure rotation extends fm_tr s s :=
  (rotation_no_displacement : ∀ v : vectr s, ∥(to_fm_tr.transform_vectr 0)∥ = 0)
  (rotation_no_scaling : ∀ v : vectr s, ∥(to_fm_tr.transform_vectr v)∥ = 1) 
  (rotation_col_orthogonal : ∀ i j : fin dim, 
        i≠j →
        ⟪ to_fm_tr.transform_vectr (⟨(fm.base dim id_vec).basis.basis_vecs i⟩:vectr s),
          to_fm_tr.transform_vectr ((⟨(fm.base dim id_vec).basis.basis_vecs j⟩):vectr s)⟫ 
          = (0:ℝ))


def mk_rotation' {K : Type u} [inhabited K] [normed_field K] [has_lift_t K ℝ]
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} {s : spc K f} (b : vectr_basis s) : rotation s :=
⟨ 
  begin
    
    eapply fm_tr.mk,
    split,
    {
      intros,
      dsimp only [has_vadd.vadd, add_vectr_point, aff_vec_group_action, add_vec_pt, mk_point'],
      sorry
    },
    split,
    {
      dsimp only [function.left_inverse],
      intros,
      sorry
    },
    {
      dsimp only [function.right_inverse, function.left_inverse],
      intros,
      sorry
    },
    exact (λ p, mk_point_from_coords (b.to_matrix.mul_vec p.to_coords)),
    exact (λ p, mk_point_from_coords (b.to_matrix.cramer_inverse.mul_vec p.to_coords)),

         --(λ p, mk_point_from_coords (b.to_matrix.mul_vec p.to_coords)),
          --(λ p, mk_point_from_coords ((b.to_matrix.cramer_inverse.mul_vec p.to_coords)),
    split,
    {
      intros,
      sorry
    },
    {
      intros,
      sorry,
    },
    {
      dsimp only [function.left_inverse],
      intros,
      sorry
    },
    {
      dsimp only [function.right_inverse, function.left_inverse],
      intros,
      sorry
    },
    exact (λ v, mk_vectr_from_coords (b.to_matrix.mul_vec v.to_coords)),
    exact (λ p, mk_vectr_from_coords (b.to_matrix.cramer_inverse.mul_vec p.to_coords)),
  end
,begin
  intro h,
  dsimp only [fm_tr.transform_vectr],
  simp only [mk_vec, mk_pt, equiv.coe_fn_mk, norm_eq_zero],
  dsimp only [has_zero.zero],
  dsimp only [vectr_zero, mk_vectr, mk_vec_n, mk_vec],
  simp only,
  sorry,
end, sorry, sorry⟩

def mk_rotation (ortho_vectrs : fin dim → vectr s) : rotation s :=
  (mk_rotation' ⟨ortho_vectrs, sorry, sorry⟩)


instance : has_lift_t (orientation s) (rotation s) := ⟨λo, mk_rotation' o.1/-subtype notation-/⟩