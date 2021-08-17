--import .....math.affine.aff_coord_space
import data.real.basic

namespace scalar

/-
Algebraic types of scalars for different physical dimensions.
Deprecated. Use basicDimScalarType.

TODO: Rethink use of abbreviation
-/
abbreviation length := ℝ 
abbreviation time := ℝ 
abbreviation mass := { r : ℝ // r >= 0}
abbreviation current := ℝ 
abbreviation temperature := { r : ℝ // r >= 0} -- how/where to say can't be equivalent to negative in Kelvin?  
abbreviation quantity := ℕ 
abbreviation intensity := {r : ℝ // r >= 0}    -- is this right?

-- Proof that adding two masses together is a valid operation
def add_mass : mass → mass → mass 
| m1 m2 := ⟨m1.1 + m2.1, begin
  cases m1, cases m2, simp,
  apply add_nonneg,
  assumption, assumption,
end ⟩

-- Proof that adding two intensities together is a valid operation
def add_intensity : intensity → intensity → intensity 
| i1 i2 := ⟨i1.1 + i2.1, begin
  cases i1, cases i2, simp,
  apply add_nonneg,
  assumption, assumption,
end ⟩

-- Proof that adding two temperatures together is a valid operation
def add_temperature : temperature → temperature → temperature 
| t1 t2 := ⟨t1.1 + t2.1, begin
  cases t1, cases t2, simp,
  apply add_nonneg,
  assumption, assumption,
end ⟩

-- Proof that subtracting a smaller mass from a larger mass is valid
def sub_mass (m1 m2 : mass) (h : m1 >= m2) : mass :=
⟨m1.1 - m2.1, begin 
  cases m1, cases m2, simp, 
  exact h,
end ⟩

-- Proof that subtracting a smaller intensity from a larger intensity is valid
def sub_intensity (i1 i2 : intensity) (h : i1 >= i2) : intensity :=
⟨i1.1 - i2.1, begin
  cases i1, cases i2, simp,
  exact h,
end ⟩

-- Proof that subtracting a smaller temperature from a larger temperature is valid
def sub_temperature (t1 t2 : temperature) (h : t1 >= t2) : temperature :=
⟨t1.1 - t2.1, begin
  cases t1, cases t2, simp,
  exact h,
end ⟩

-- Proof that multiplying mass is valid
def mul_mass : mass → mass → mass 
| m1 m2 := ⟨m1.1 * m2.1, begin
  cases m1, cases m2, simp,
  apply mul_nonneg,
  assumption, assumption,
end ⟩

-- Proof that multiplying intensity is valid
def mul_intensity : intensity → intensity → intensity 
| i1 i2 := ⟨i1.1 * i2.1, begin
  cases i1, cases i2, simp,
  apply mul_nonneg,
  assumption, assumption,
end ⟩

-- Proof that multiplying temperature is valid
def mul_temperature : temperature → temperature → temperature 
| i1 i2 := ⟨i1.1 * i2.1, begin
  cases i1, cases i2, simp,
  apply mul_nonneg,
  assumption, assumption,
end ⟩


end scalar