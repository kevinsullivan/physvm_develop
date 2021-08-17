/-
© 2021 by the Rector and Visitors of the University of Virginia
-/

import algebra.module.basic
import linear_algebra.affine_space.affine_equiv

-- Let K be a non-empty field
universes u 
variables (K : Type u) [field K] [inhabited K]


lemma add_smul_l2 : ∀ (r s : K) (x : K × K), (r + s) • x = r • x + s • x := 
begin
  intros,
  ext,
  simp *,
  exact right_distrib r s _,
  simp *,
  exact right_distrib r s _,
end
lemma zero_smul_l2 : ∀ (x : K × K), (0 : K) • x = 0 := 
begin
  intros,
  ext,
  simp *,
  simp *,
end

instance module_K_KxK : module K (K × K) := 
⟨ add_smul_l2 K, zero_smul_l2 K ⟩ 

