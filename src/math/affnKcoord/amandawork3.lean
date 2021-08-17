import data.real.basic
import .affnK
import tactic.linarith
/-
Amanda:

Go to line 730ish and find the proof I just copied and pasted in. It is an example basis proof. 
Dig into the details and you'll be able to adapt this, or at least some of it.
-/
import linear_algebra.basis
-- Testing vec_n_basis
⁻¹ 
/-
protected noncomputable def span : basis ι R (span R (range v)) :=
basis.mk (linear_independent_span hli) $
begin
  rw eq_top_iff,
  intros x _,
  have h₁ : subtype.val '' set.range (λ i, subtype.mk (v i) _) = range v,
  { rw ← set.range_comp },
  have h₂ : map (submodule.subtype _) (span R (set.range (λ i, subtype.mk (v i) _)))
    = span R (range v),
  { rw [← span_image, submodule.subtype_eq_val, h₁] },
  have h₃ : (x : M) ∈ map (submodule.subtype _) (span R (set.range (λ i, subtype.mk (v i) _))),
  { rw h₂, apply subtype.mem x },
  rcases mem_map.1 h₃ with ⟨y, hy₁, hy₂⟩,
  have h_x_eq_y : x = y,
  { rw [subtype.ext_iff, ← hy₂], simp },
  rwa h_x_eq_y
end
-/
→ 
open submodule
/-

protected theorem lt_asymm {n m : ℕ} (h₁ : n < m) : ¬ m < n :=
le_lt_antisymm (nat.le_of_lt h₁)

∘
-/
@[simp]
lemma eznat :  ∀ (a b : ℕ), a + b < a → false := 
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
lemma eznat2 :  ∀ (a b : ℕ), b + a < a → false := 
begin
  intros a b c,
  rw ←(nat.add_comm a b) at c,
  exact eznat _ _ c,
end

#check nat.add_comm


#check nat.succ_ne_zero
#check nat.add_lt_add_left
#check lt_trans

#check finset.sum

#check nat.add_lt_add_left

def fin0notnonempty : ¬nonempty (fin 0) := begin
  by_contradiction,
  cases h,
  cases h,
    let : ¬h_val < 0 := nat.not_lt_zero _,
    contradiction
end
#check absurd

#check @linear_independent_fin_cons ℚ (vec_n ℚ 2) _ _ _ 

#check @linear_independent_empty_type (fin 0) ℚ (vec_n ℚ 1) sorry _ _ _ fin0notnonempty

#check submodule
#check module

#check submodule.

#check finset.not_mem_empty
#check set.not_mem_empty

#check set

#check submodule.span

#check funext

#check ext

def vec_1_basis := 
let v := (λ a : fin 1, (λ b : fin 1, vec.mk (1 : ℚ)))  in
  vec_n_basis.mk v
begin
  /-
lemma linear_independent_fin_cons {n} {v : fin n → V} :
  linear_independent K (fin.cons x v : fin (n + 1) → V) ↔
    linear_independent K v ∧ x ∉ submodule.span K (range v)
  -/
  let empty_basis : fin 0 → vec_n ℚ 1 := begin
    assume f0,
    cases f0,
    let : ¬f0_val < 0 := nat.not_lt_zero _,
    contradiction,
  end,
  let empli : linear_independent ℚ empty_basis :=
    @linear_independent_empty_type (fin 0) ℚ (vec_n ℚ 1) _ _ _ _ fin0notnonempty,
  let consb : fin 1 → vec_n ℚ 1 := (fin.cons (v ⟨0, by linarith⟩) empty_basis),
  let consbeqv : consb = v := begin
    suffices feh : ∀i, consb i = v i, from funext feh,
    intros,
    cases i,
    cases i_val,
    refl,
    let ht :  i_val + 1 = i_val.succ := by repeat { apply nat.add_one _ },
          rw ←ht at i_property,
          let : false := by exact eznat2 _ _ i_property,
    contradiction,
    /-
    
          let ht :  i_val + 2 = i_val.succ.succ := by repeat { apply nat.add_one _ },
          rw ←ht at i_property,
          let : false := by exact eznat2 _ _ i_property,
    -/
  end,
  let licons : linear_independent ℚ consb := 
  begin
    apply (@linear_independent_fin_cons ℚ (vec_n ℚ 1) _ _ _ (v ⟨0, by linarith⟩) _ empty_basis).mpr,
    split,
    exact empli,
    dsimp only [submodule.span, Inf],
    dsimp only [coe_sort, has_coe_to_sort.coe, coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, set_like.coe],
    dsimp only [set.range, set.Inter],
    --simp *,
    dsimp only [infi, Inf, complete_semilattice_Inf.Inf, complete_lattice.Inf, set.range],
    simp only [forall_apply_eq_imp_iff', and_imp, fin.mk_zero, exists_prop, nat.not_lt_zero, add_zero, int.coe_nat_zero, id.def,
    ge_iff_le, int.coe_nat_one, set_like.mem_coe, set.mem_set_of_eq, mem_carrier, exists_imp_distrib,
    has_subset.subset, set.subset],
    dsimp [set_of, has_mem.mem, set.mem],
    assume a,
    let empvecs : set (vec_n ℚ 1) := ∅,
    let empsm := @submodule.span ℚ (vec_n ℚ 1) _ _ _ ∅,
    let empsmemp := @submodule.span_empty ℚ (vec_n ℚ 1) _ _ _,
    let empsmeqbot : empsm = ⊥ := by simp *,
    let app_ := a ⊥,
    let huh : (∀ (a : fin 0), (↑(⊥ : submodule ℚ (vec_n ℚ 1)) : set _) (empty_basis a)) := begin
      intros f0,
      cases f0,
      let : ¬f0_val < 0 := nat.not_lt_zero _,
      contradiction,
    end,
    let hmm := app_ huh,
    let veq0 : (v 0) = 0 := (@mem_bot ℚ (vec_n ℚ 1) _ _ _ _).mp hmm, 
    let vneq0_0 : (v 0 0) ≠ 0 := begin
      simp *,
      unfold has_zero.zero,
      dsimp [vec_zero ℚ],
      assume h,
      injection h, revert h_1,
      dec_trivial,
    end, 
    let veq0_0 : (v 0 0) = 0 := begin
      rw veq0,
      refl,
    end, 
    contradiction
    --intros a,
    /-let h2 : ((λ (a : vec_n ℚ 1), ∀ (a_1 : submodule ℚ (vec_n ℚ 1)), 
              (∀ (a : fin 0), empty_basis a ∈ a_1) → a ∈ a_1) : set (vec_n ℚ 1)) (v 0)
      := 
        begin 
          let h3 : _ := (mem_carrier ({carrier := λ (a : vec_n ℚ 1), ∀ (a_1 : submodule ℚ (vec_n ℚ 1)), 
          (∀ (a : fin 0), empty_basis a ∈ a_1) → a ∈ a_1, zero_mem' := _, add_mem' := _, smul_mem' := _} 
            : submodule ℚ (vec_n ℚ 1))).mpr h,

        end,
    let h1 
      : h0 = ∅ 
      := by admit,-/
  end,
  rw consbeqv at licons,
  exact licons,
--#check not
 -- eapply
--#check ∉ 
  /-
  
theorem linear_independent_iff' : linear_independent R v ↔
  ∀ s : finset ι, ∀ g : ι → R, ∑ i in s, g i • v i = 0 → ∀ i ∈ s, g i = 0 :=
  -/
  /-
  eapply (@linear_independent_iff' (fin 1) ℚ (vec_n ℚ 1) v _ _ _).mpr,
  intros a b c d e,-/
/-

lemma sum_range_succ {β} [add_comm_monoid β] (f : ℕ → β) (n : ℕ) :
  ∑ x in range (n + 1), f x = ∑ x in range n, f x + f n :=
by simp only [add_comm, sum_range_succ_comm]
-/
  --unfold finset.sum at *,
 -- revert c,
  --unfold_projs,
  --dsimp [finset.sum] at c,
  
  /-ext,
  split,
  {
    /-intro h,
    dsimp only [has_bot.bot, has_zero.zero, add_zero_class.zero, add_monoid.zero, add_comm_monoid.zero],
    suffices h' : x = {support := ∅, to_fun := λ (_x : fin 1), semiring.zero, mem_support_to_fun := _},
    exact h',
    dsimp only [linear_map.ker, submodule.comap, set.preimage] at h,
    have h₀ : ⇑(finsupp.total (fin 1) (vec_n ℚ 1) ℚ (λ (a b : fin 1), {coord := 1})) x ∈ ↑⊥ := by exact h,
    dsimp only [has_bot.bot, has_zero.zero, add_zero_class.zero, add_monoid.zero, add_comm_monoid.zero] at h₀,
    dsimp only [vec_zero] at h₀,
    have h₁ : ⇑(finsupp.total (fin 1) (vec_n ℚ 1) ℚ (λ (a b : fin 1), {coord := 1})) x = λ (_x : fin 1), mk_vec ℚ 0 := by exact h₀,
    dsimp only [finsupp.total, finsupp.lsum, coe_fn, has_coe_to_fun.coe] at h₁,
    dsimp [finsupp.sum] at h₁,
    simp only [linear_map.id_coe, id.def] at h₁,
    sorry,-/
  },
  {
    intro h,
    dsimp only [has_bot.bot, has_zero.zero, add_zero_class.zero, add_monoid.zero, add_comm_monoid.zero] at h,
    have h₀ : x = {support := ∅, to_fun := λ (_x : fin 1), semiring.zero, mem_support_to_fun := _} := by exact h,
    dsimp only [linear_map.ker, submodule.comap, set.preimage],
    suffices h' : ⇑(finsupp.total (fin 1) (vec_n ℚ 1) ℚ (λ (a b : fin 1), {coord := 1})) x ∈ ↑⊥,
    exact h',
    dsimp only [has_bot.bot, has_zero.zero, add_zero_class.zero, add_monoid.zero, add_comm_monoid.zero],
    dsimp only [vec_zero],
    suffices h' : ⇑(finsupp.total (fin 1) (vec_n ℚ 1) ℚ (λ (a b : fin 1), {coord := 1})) x = λ (_x : fin 1), mk_vec ℚ 0,
    exact h',
    dsimp only [finsupp.total, finsupp.lsum, coe_fn, has_coe_to_fun.coe],
    rw h₀,
    dsimp [finsupp.sum],
    refl,
  }-/
end begin
  dsimp only [submodule.span, Inf],
  dsimp only [has_top.top, set.univ],
  dsimp only [coe_sort, has_coe_to_sort.coe, coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, set_like.coe],
  dsimp only [set.range, set.Inter],
  simp only [nonempty_of_inhabited, set.mem_set_of_eq, exists_const],
  ext,
  split,
  {
    intro,
    exact true.intro,
  },
  {
    intro,
    dsimp only [infi, Inf, complete_semilattice_Inf.Inf, complete_lattice.Inf, set.range],
    simp *,
    dsimp [set_of],
    intros f g,
    simp [has_subset.subset, set.subset] at g,
    /-
    (λ (a : vec_n ℚ 2), 
      (∀ ⦃a : vec_n ℚ 2⦄, 
        (a ∈ λ (x : vec_n ℚ 2), 
          ∃ (y : fin 2), (λ (j : fin 2), ite (y = j) {coord := 1} {coord := 0}) = x) 
            → a ∈ c.carrier) → a ∈ c) 
        = t
    -/
    let h3 := x ⟨0, by linarith⟩,
    destruct h3,

    intros,
    let one_ : vec_n ℚ 1 := (λ i, {coord := 1}),


    let h4 : one_ ∈ f := by apply @g one_ rfl,
    let onex := coord•one_,
    let onexmem : onex ∈ f := 
      by exact @submodule.smul_mem ℚ (vec_n ℚ 1) _ _ _ f one_ coord h4,
    haveI := onex,
    let h6 : coord • (λ (i : fin 1), {coord := 1} : vec_n ℚ 1) = onex := rfl,
    let onexeq : (∀ (i : fin 1), x i = onex i) := begin
        intros,
        cases i,
        cases i_val,
        { rw ←h6,
          let h7 : (coord • (λ (i : fin 1), {coord := 1}) : vec_n ℚ 1) ⟨0, i_property⟩
            = (coord • {coord := 1}) := begin
              refl
            end,
          simp [h7],
          dsimp [has_scalar.smul],
          simp *,
          let h16 : x 0 = h3 := by refl,
          rw h16,
          exact a,
         },
        {
          cases i_val,
          let h10 : (1 )= (1) := rfl,
          let h11 := lt_irrefl 1,
          contradiction,

          let h12 : 1 < i_val.succ.succ := by exact nat.one_lt_succ_succ i_val,
          let h13 : 1 < 1 := by exact lt_trans h12 i_property,
          let h14 : ¬1<1 := by exact lt_irrefl _,
          contradiction,
        },
    end,
    let h20 : x = onex := by exact funext onexeq,
    rw h20,
    exact onexmem,

  },
end


#check submodule.span


def vec_2_basis := 
let v := (λ i : fin 2, (λ j : fin 2, 
  if i = j then mk_vec ℚ 1 else mk_vec ℚ 0
))  in
  vec_n_basis.mk v
begin
  /-
lemma linear_independent_fin_cons {n} {v : fin n → V} :
  linear_independent K (fin.cons x v : fin (n + 1) → V) ↔
    linear_independent K v ∧ x ∉ submodule.span K (range v)
  -/
  let empty_basis : fin 0 → vec_n ℚ 2 := begin
    assume f0,
    cases f0,
    let : ¬f0_val < 0 := nat.not_lt_zero _,
    contradiction,
  end,
  let empli : linear_independent ℚ empty_basis :=
    @linear_independent_empty_type (fin 0) ℚ (vec_n ℚ 2) _ _ _ _ fin0notnonempty,
  let consb : fin 1 → vec_n ℚ 2 := (fin.cons (v ⟨0, by linarith⟩) empty_basis),
  let consb3 : fin 2 → vec_n ℚ 2 := (fin.snoc consb (v ⟨1, by linarith⟩)),
  
  
  /-let consbeqv : consb = v := begin
    suffices feh : ∀i, consb i = v i, from funext feh,
    intros,
    cases i,
    cases i_val,
    refl,
    let ht :  i_val + 1 = i_val.succ := by repeat { apply nat.add_one _ },
          rw ←ht at i_property,
          let : false := by exact eznat2 _ _ i_property,
    contradiction,
    /-
    
          let ht :  i_val + 2 = i_val.succ.succ := by repeat { apply nat.add_one _ },
          rw ←ht at i_property,
          let : false := by exact eznat2 _ _ i_property,
    -/
  end,-/
  let licons : linear_independent ℚ consb := 
  begin
    apply (@linear_independent_fin_cons ℚ (vec_n ℚ 2) _ _ _ (v ⟨0, by linarith⟩) _ empty_basis).mpr,
    split,
    exact empli,
    dsimp only [submodule.span, Inf],
    dsimp only [coe_sort, has_coe_to_sort.coe, coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, set_like.coe],
    dsimp only [set.range, set.Inter],
    --simp *,
    dsimp only [infi, Inf, complete_semilattice_Inf.Inf, complete_lattice.Inf, set.range],
    simp only [forall_apply_eq_imp_iff', and_imp, fin.mk_zero, exists_prop, nat.not_lt_zero, add_zero, int.coe_nat_zero, id.def,
    ge_iff_le, int.coe_nat_one, set_like.mem_coe, set.mem_set_of_eq, mem_carrier, exists_imp_distrib,
    has_subset.subset, set.subset],
    dsimp [set_of, has_mem.mem, set.mem],
    assume a,
    let empvecs : set (vec_n ℚ 2) := ∅,
    let empsm := @submodule.span ℚ (vec_n ℚ 2) _ _ _ ∅,
    let empsmemp := @submodule.span_empty ℚ (vec_n ℚ 2) _ _ _,
    let empsmeqbot : empsm = ⊥ := by simp *,
    let app_ := a ⊥,
    let huh : (∀ (a : fin 0), (↑(⊥ : submodule ℚ (vec_n ℚ 2)) : set _) (empty_basis a)) := begin
      intros f0,
      cases f0,
      let : ¬f0_val < 0 := nat.not_lt_zero _,
      contradiction,
    end,
    let hmm := app_ huh,
    let veq0 : (v 0) = 0 := (@mem_bot ℚ (vec_n ℚ 2) _ _ _ _).mp hmm, 
    let vneq0_0 : (v 0 0) ≠ 0 := begin
      simp *,
      unfold has_zero.zero,
      dsimp [vec_zero ℚ],
      assume h,
      injection h, revert h_1,
      dec_trivial,
    end, 
    let veq0_0 : (v 0 0) = 0 := begin
      rw veq0,
      refl,
    end, 
    contradiction
  end,  
  let consb2 : fin 2 → vec_n ℚ 2 := (fin.snoc consb (v ⟨1, by linarith⟩)),
  let licons2 : linear_independent ℚ consb2 := 
  begin
    apply (@linear_independent_fin_snoc ℚ (vec_n ℚ 2) _ _ _ (v ⟨1, by linarith⟩) _ consb).mpr,
    split,
    exact licons,
    let span_ := span ℚ (set.range consb),
    dsimp only [submodule.span, Inf],
    dsimp only [coe_sort, has_coe_to_sort.coe, coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, set_like.coe],
    dsimp only [set.range, set.Inter],
    --simp *,
    dsimp only [infi, Inf, complete_semilattice_Inf.Inf, complete_lattice.Inf, set.range],
    simp only [forall_apply_eq_imp_iff', and_imp, fin.mk_zero, exists_prop, nat.not_lt_zero, add_zero, int.coe_nat_zero, id.def,
    ge_iff_le, int.coe_nat_one, set_like.mem_coe, set.mem_set_of_eq, mem_carrier, exists_imp_distrib,
    has_subset.subset, set.subset],
    dsimp [set_of, has_mem.mem, set.mem],
    assume a,

  end
end
begin
  dsimp only [submodule.span, Inf],
  dsimp only [has_top.top, set.univ],
  dsimp only [coe_sort, has_coe_to_sort.coe, coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, set_like.coe],
  dsimp only [set.range, set.Inter],
  simp only [nonempty_of_inhabited, set.mem_set_of_eq, exists_const],
  ext,
  split,
  {
    intros,
    exact true.intro,
  },
  {
    intros,
    intro,
    dsimp only [infi, Inf, complete_semilattice_Inf.Inf, complete_lattice.Inf, set.range],
    simp *,
    dsimp [set_of],
    intros c d,
    dsimp [has_subset.subset, set.subset] at d,--, has_mem.mem, set.mem] at d,
    --rw ←d at t,
    --rw d.symm,
    let smdef : set (vec_n ℚ 2) := 
      (λ (a : vec_n ℚ 2), 
      (∀ ⦃a : vec_n ℚ 2⦄, (∃ (y : fin 2), 
        (λ (j : fin 2), ite (y = j) ({coord := 1}: vec ℚ) ({coord := 0}: vec ℚ)
        ) = a) → c.carrier a) 
          → (↑c : set _) a),
    let tt : t = smdef := by exact d.symm,
    simp *,
    dsimp [has_mem.mem, set.mem],
    assume cmem : _,
    let v0 := v ⟨0, by linarith⟩,
    let v1 := v ⟨1, by linarith⟩,
    let v0mem : v0 ∈ c := begin
      --let h0 : 
      let c0 : vec_n ℚ 2 := 
        (λ (j : fin 2), ite (0 = j) ({coord := 1}: vec ℚ) ({coord := 0}: vec ℚ)),
      let h0 : c.carrier c0 := cmem 0,
      let h1 : c0 = v0 :=
        begin
          suffices sh : ∀ i, c0 i = v0 i, from funext sh,
          intros,
          cases i,
          cases i_val,
          refl,
          cases i_val,
          refl,
          let ht :  i_val + 2 = i_val.succ.succ := by repeat { apply nat.add_one _ },
          rw ←ht at i_property,
          let : false := by exact eznat2 _ _ i_property,
          contradiction,
        end,  
      rw ←h1,    
      exact (mem_carrier c).mp h0,
    end, 
    let v1mem : v1 ∈ c := begin
      --let h0 : 
      let c1 : vec_n ℚ 2 := 
        (λ (j : fin 2), ite (1 = j) ({coord := 1}: vec ℚ) ({coord := 0}: vec ℚ)),
      let h0 : c.carrier c1 := cmem ⟨1, by linarith⟩,
      let h1 : c1 = v1 :=
        begin
          suffices sh : ∀ i, c1 i = v1 i, from funext sh,
          intros,
          cases i,
          cases i_val,
          refl,
          cases i_val,
          refl,
          let ht :  i_val + 2 = i_val.succ.succ := by repeat { apply nat.add_one _ },
          rw ←ht at i_property,
          let : false := by exact eznat2 _ _ i_property,
          contradiction,
        end,  
      rw ←h1,    
      exact (mem_carrier c).mp h0,
    end, 
    
    --let x0 := x ⟨0, by linarith⟩, 
    --let x1 := x ⟨1, by linarith⟩,
    destruct x ⟨0, by linarith⟩,
    intros c0 e0,
    destruct x ⟨1, by linarith⟩,
    intros c1 e1,
    let c0smulv0 := λ (j : fin 2), ite (0 = j) ({coord := c0}: vec ℚ) ({coord := 0}: vec ℚ),
    let c0smulv0_eq :
      (c0 • v0 = c0smulv0)
        := begin
         -- simp *,
          suffices sh : ∀ i, (c0 • v0) i = c0smulv0 i, from funext sh,
          intros,
          cases i,
          cases i_val,
          simp *,
          let h0 : ite (0 = 0) ({coord := c0} : vec ℚ) ({coord := 0} : vec ℚ) = ({coord := c0} : vec ℚ) := rfl,
          simp *, 
          dsimp [has_scalar.smul],
          simp *,
          cases i_val,
          simp *,
          let h0 : ite (1 = 0) ({coord := c0} : vec ℚ) ({coord := 0} : vec ℚ) = ({coord := 0} : vec ℚ) := rfl,
          simp *, 
          dsimp [has_scalar.smul],
          simp *,
          let ht :  i_val + 2 = i_val.succ.succ := by repeat { apply nat.add_one _ },
          rw ←ht at i_property,
          let : false := by exact eznat2 _ _ i_property,
          contradiction,

        end,
    let c0smulv0mem : c0smulv0 ∈ c := 
      begin 
        rw ←c0smulv0_eq,
        exact @submodule.smul_mem ℚ (vec_n ℚ 2) _ _ _ c v0 c0 v0mem
      end,

    let c1smulv1 := λ (j : fin 2), ite (1 = j) ({coord := c1}: vec ℚ) ({coord := 0}: vec ℚ),

    let c1smulv1_eq :
      (c1 • v1 = c1smulv1)
        := begin
         -- simp *,
          suffices sh : ∀ i, (c1 • v1) i = c1smulv1 i, from funext sh,
          intros,
          cases i,
          cases i_val,
          simp *,
          --let h0 : ite (1 = 0) ({coord := c1} : vec ℚ) ({coord := 0} : vec ℚ) = ({coord := c1} : vec ℚ) := rfl,
          --simp *, 
          dsimp [has_scalar.smul],
          simp *,
          cases i_val,
          simp *,
          --let h0 : ite (0 = 0) ({coord := c1} : vec ℚ) ({coord := 0} : vec ℚ) = ({coord := 0} : vec ℚ) := rfl,
          --simp *, 
          dsimp [has_scalar.smul],
          simp *,
          let ht :  i_val + 2 = i_val.succ.succ := by repeat { apply nat.add_one _ },
          rw ←ht at i_property,
          let : false := by exact eznat2 _ _ i_property,
          contradiction,

        end,
    let c1smulv1mem : c1smulv1 ∈ c := 
      begin 
        rw ←c1smulv1_eq,
        exact @submodule.smul_mem ℚ (vec_n ℚ 2) _ _ _ c v1 c1 v1mem
      end,

    let comb_mem : c0smulv0 + c1smulv1 ∈ c :=
      by exact @submodule.add_mem ℚ (vec_n ℚ 2) _ _ _ c  _ _ c0smulv0mem c1smulv1mem,

    let x_combeq : x = c0smulv0 + c1smulv1 := begin
      suffices sh : ∀ i, x i = (c0smulv0 + c1smulv1) i, from funext sh,
      intros,
      cases i,
      cases i_val,
      /-
      x ⟨0, i_property⟩ = (c0smulv0 + c1smulv1) ⟨0, i_property⟩
      -/
      rw e0,
      simp *, refl,
      cases i_val,
      rw e1,
      simp *, refl,
      let ht :  i_val + 2 = i_val.succ.succ := by repeat { apply nat.add_one _ },
      rw ←ht at i_property,
      let : false := by exact eznat2 _ _ i_property,
      contradiction,
    end,
     
    rw x_combeq,
    exact comb_mem,
  }
end



def vec_2_basis_hard := 
let v := (λ i : fin 2, 
  if i = 0 then mk_vec_n ℚ 2 ⟨[4, 3],rfl⟩ else mk_vec_n ℚ 2 ⟨[-1, 1],rfl⟩) 
  in
  vec_n_basis.mk v
  begin

  end
  begin

  end


#check @fintype.linear_independent_iff (fin 2) ℚ (vec_n ℚ 2) sorry _ _ _ _

variables (sm : submodule ℚ (vec_n ℚ 1)) (v : (vec_n ℚ 1))

let h15 := funext one

#check @linear_independent_iff' (fin 1) ℚ (vec_n ℚ 1) sorry _ _ _

#check nat.add_succ_sub_one

#check funext
#check (1:ℚ) • v

#check ↑(finset.range 3)

#check nat.add_succ_lt_add
#check nat.succ_succ_ne_one

#check smul_prod

#check lt_tra

#check lt_one_add
#check nat.lt_add_left

#check nat.succ_succ

#check iff.mpr

#check lt_add_one

#check nat.succ


#check submodule
/-
(
  λ (a : vec_n ℚ 2),
  (∀ ⦃a : vec_n ℚ 2⦄,
    set.mem a
    (
      λ (x : vec_n ℚ 2), 
      ∃ (y : fin 2), 
      (
        λ (j : fin 2), 
        ite (y = j) {coord := 1} {coord := 0}
      ) 
      = x
    ) 
    →
    set.mem a c.carrier
  ) 
  →
  set.mem a ↑c
) 
= t

-/

#check nat.lt_add_of_zero_lt_left

#check @submodule.smul_mem

#check smul_add

#check finset

#check v ∈ sm

#check (↑sm:set (vec_n ℚ 1)) v

def dajks : fin 2 → ℕ 
| ⟨0, _⟩ := 1
| ⟨1, _⟩ := 2
| ⟨n, _⟩ := 0

def dasjsj : ∀i ∈ finset.range 2, ℕ 
:= λi : _, λ j, begin
  cases i,
  exact 0,
  cases i,
  exact 0,
  cases i,

end

#check nat.lt


#check nat_ceil_lt_add_one
#check nat_mul_inj

#check lt_irrefl

#check lt_add_one
#check submodule

#check module

#check {[1]} ⊆  {[1], [2]}

#check ⦃a : vec_n ℚ 1⦄
  
#check eq_bot_iff

#check eq

#check set.set_of_mem_eq


def n := 1
def K := ℚ


def myfinset : finset ℕ := finset.range 4
@[reducible]
abbreviation pt_nf := ∀i ∈{i|i∈myfinset}, pt ℚ
@[reducible]
abbreviation vec_nf := fin (n) → vec ℚ

#check set.range



#eval 0 ∈ myfinset
#eval myfinset



def mk_pt_nf (vals : vector ℚ n) : pt_nf := 
  λj : _, λmf:_, begin

  end

def mk_vec_nf (vals : vector ℚ n) : vec_nf ℚ n := 
  λi, mk_vec ℚ (vals.nth i)

def pt_nf.coords
 (ptn : pt_nf ) : fin n → ℚ :=
  λi : fin n, (ptn i).coord

def vec_nf.coords (vecn : vec_nf ) : fin n → K :=
  λi, (vecn i).coord


structure vec_nf_basis :=
  (basis_vecs:fin n → vec_nf )
  (basis_independent : linear_independent ℚ basis_vecs)
  (basis_spans : submodule.span ℚ (set.range basis_vecs) = ⊤)

instance : has_lift_t (vec_nf_basis K n) (fin n → vec_n K n) := ⟨λvb, vb.basis_vecs⟩

open_locale affine
--done
instance : add_comm_group (vec_nf) := by apply_instance
instance : affine_space (vec_nf) (pt_nf) := by apply_instance


/-
Frame built from primitive (fin n)-indexed maps pts and vecs.
Constructors are Base (standard) frame or a derived frame.
-/
inductive fm : Π (dim : ℕ) , Type 
| base : Π (dim : ℕ), fm dim

@[simp]
def fm.basis 
{dim : ℕ} :
fm  dim → (vec_n_basis ℚ dim)
| (fm.base dim ) := ⟨(λ i j, if j = i then mk_vec K 1 else mk_vec K 0), sorry, sorry⟩