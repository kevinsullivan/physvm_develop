import analysis.normed_space.real_inner_product
import ..affine.aff_coord_space

variable n : ℕ

/-! ### rfl lemmas and prerequisite lemmas -/




/-! ### lemmas necessary to show type class instances -/




/-! ### type class instances -/

--first implement inner product (dot product)
instance : has_inner (aff_vec_coord_tuple ℝ n) := sorry

--have to first prove all associated arguments
instance : inner_product_space (aff_vec_coord_tuple ℝ n) := sorry

-- feature/euclid

/-!
    Goal for Wednesday: fill out this file, put sorry's where you have to
    Goal for Saturday: fill out as many sorry's as possible

    p.s. see if the dot product is defined somewhere. Might be under the 
    `linear_algebra` folder, don't want to have to reinvent the wheel
-/
