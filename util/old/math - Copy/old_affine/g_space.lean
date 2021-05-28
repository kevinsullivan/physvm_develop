import group_theory.group_action
import ..affine.add_group_action

-- g-spaces

/-!
# G-spaces, Homogeneous spaces, and torsors

A `G-space` is a nonempty set `X` on which a group `G` acts.
A `Homogeneous Space` is a G-space where the group action is transitive.
A `Torsor` is a homogeneous space where the group action is also free.

All of these things are implemented w.r.t. both additive and multiplicative groups. The theory
is equivalent for both.
-/


/-- g-space w.r.t. multiplicative action. -/
class mul_space (G X : Type*) [group G] extends mul_action G X

/-- g-space w.r.t. additive action. -/
class add_space (G X : Type*) [add_group G] extends add_action G X


/-- homogeneous spaces w.r.t. multiplicative action. -/
class mul_homogeneous_space (G X : Type*) [group G] extends mul_space G X :=
(mul_trans : ∀ x y : X, ∃ g : G, g • x = y)

/-- homogeneous spaces w.r.t. additive action. -/
class add_homogeneous_space (G X : Type*) [add_group G] extends add_space G X :=
(add_trans : ∀ x y : X, ∃ g : G, g ⊹ x = y)


/-- torsors w.r.t. multiplicative action. -/
class mul_torsor (G X : Type*) [group G] extends mul_homogeneous_space G X :=
(mul_free : ∀ x : X, ∀ g h : G, g • x = h • x → g = h)

/-- torsors w.r.t. additive action. -/
class add_torsor (G X : Type*) [add_group G] extends add_space G X :=
(add_free : ∀ x : X, ∀ g h : G, g ⊹ x = h ⊹ x → g = h)

-- TODO: mul_ and add_torsor with diff function

universes u v
variables (X : Type u) (G : Type v) [add_group G] [add_torsor G X]

#check exists_unique

lemma add_trans_free_unique : ∀ x y : X, ∃! g : G, g ⊹ x = y := sorry
