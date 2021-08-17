import .affnK
import .affnKcoord_vectorspace

/-
    ********************
    *** Affine space ***
    ********************
-/
universes u
open_locale affine

section implicitK
variables 
{K : Type u} [field K] [inhabited K] 
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} (s : spc K f)
{dim2 : nat } {id_vec2 : fin dim2 → nat} {f2 : fm K dim2 id_vec2} (s2 : spc K f2)


/-
Definitions of affine operations
-/
@[simp]
def sub_point_point (p1 p2 : point s) : vectr s := mk_vectr' s (p1.coords -ᵥ p2.coords)
@[simp]
def add_point_vectr (p : point s) (v : vectr s) : point s := 
    mk_point' s (v.coords +ᵥ p.coords) -- reorder assumes order is irrelevant
@[simp]
def add_vectr_point (v : vectr s) (p : point s) : point s := 
    mk_point' s (v.coords +ᵥ p.coords)

instance : has_vadd (vectr s) (point s) := ⟨add_vectr_point s⟩
/-
The 0 vectr plus any particular point is the particular point unchanged
-/
lemma zero_vectr_vadd'_a1 : ∀ p : point s, (0 : vectr s) +ᵥ p = p := begin
    intros,
    ext,
    dsimp only [has_vadd.vadd],
    dsimp only [add_vectr_point, mk_point'],
    dsimp only [has_vadd.vadd],
    dsimp only [aff_vec_group_action, add_vec_pt],
    simp only [add_right_eq_self],
    dsimp only [has_zero.zero],
    dsimp only [vectr_zero, mk_vectr, mk_vec_n, mk_vec, vector.nth],
    simp only [list.nth_le_repeat],
    refl,
end

-- SULLIVAN: The following proof is slow to build. I simplified the
-- second simp somewhat but it's still very slow. Analyze & improve.
/-
vectr addition is associative with the action of vectrs on points
-/
lemma vectr_add_assoc'_a1 : ∀ 
    (g1 g2 : vectr s) 
    (p : point s), 
    g1 +ᵥ (g2 +ᵥ p) = g1 + g2 +ᵥ p := 
    begin
        intros, ext,
        repeat {
        have h0 : (g1 +ᵥ (g2 +ᵥ p)).coords = (g1.coords +ᵥ (g2.coords +ᵥ p.coords)) := rfl,
        have h1 : (g1 + g2 +ᵥ p).coords = (g1.coords +ᵥ g2.coords +ᵥ p.coords) := rfl,
        rw [h0,h1],
        simp *,
        simp [has_vadd.vadd, has_add.add, add_semigroup.add, add_zero_class.add,
            add_monoid.add, add_group.add, distrib.add],
        cc,
        }
    end

/-
@[protect_proj] class add_action (G : Type*) (P : Type*) [add_monoid G] extends has_vadd G P :=
(zero_vadd : ∀ p : P, (0 : G) +ᵥ p = p)
(add_vadd : ∀ (g₁ g₂ : G) (p : P), (g₁ + g₂) +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p))
-/
instance vectr_add_action: add_action (vectr s) (point s) := 
⟨ 
begin
    exact zero_vectr_vadd'_a1 s
end,
begin
    let h0 := vectr_add_assoc'_a1 s,
    intros,
    exact (h0 g₁ g₂ p).symm
end
⟩

/-
point differencing operation
-/
@[simp]
def aff_point_group_sub : point s → point s → vectr s := sub_point_point s
instance point_has_vsub : has_vsub (vectr s) (point s) := ⟨ aff_point_group_sub s ⟩ 

/-
point is a nonempty set
-/
instance : nonempty (point s) := ⟨mk_point s ⟨list.repeat 0 dim, by simp only [list.length_repeat]⟩⟩

/-
Requirement for affine spaces
-/
lemma point_vsub_vadd_a1 : ∀ (p1 p2 : (point s)), (p1 -ᵥ p2) +ᵥ p2 = p1 := begin
    intros, ext,
    dsimp only [has_vsub.vsub, has_vadd.vadd],
    dsimp only [add_vectr_point, aff_point_group_sub, mk_point', sub_point_point, mk_vectr'],
    dsimp only [has_vsub.vsub, has_vadd.vadd],
    dsimp only [aff_vec_group_action, aff_pt_group_sub, add_vec_pt, sub_pt_pt],
    simp only [add_sub_cancel'_right]
end


/-
Requirement for affine spaces
-/
lemma point_vadd_vsub_a1 : ∀ (g : vectr s) (p : point s), g +ᵥ p -ᵥ p = g := 
begin
    intros, ext,
    repeat {
    have h0 : ((g +ᵥ p -ᵥ p) : vectr s).coords = (g.coords +ᵥ p.coords -ᵥ p.coords) := rfl,
    rw h0,
    simp *,
    }
end

--final instance showing vectrs and points form an affine space
instance : affine_space (vectr s) (point s) := ⟨
    point_vsub_vadd_a1 s,
    point_vadd_vsub_a1 s,
⟩
end implicitK