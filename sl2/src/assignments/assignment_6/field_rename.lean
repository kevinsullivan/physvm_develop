import ...inClassNotes.typeclasses.algebra



/-
Inheriting two fields with same name
-/

open alg

-- need to enable "old_structure" option here

class another_two_muls (A : Type) extends mul_groupoid A renaming mul→mul1,
                                          mul_groupoid A renaming mul→mul2

instance another_two_muls_nat : another_two_muls nat := ⟨ nat.mul, nat.add ⟩ 

def nat_nat_mul1 [another_two_muls nat] (a b : ℕ) := 
another_two_muls.mul2 a b

#eval nat_nat_mul1 2 3

/-
Inheriting same field twice 
-/

class inh_mul1 (A : Type) extends mul_groupoid A := (n : ℕ)
instance inh_mul1_nat : inh_mul1 nat := ⟨ nat.mul, 3 ⟩ 

class inh_mul2 (A : Type) extends mul_groupoid A := (b : bool)
instance inh_mul2_nat : inh_mul2 nat := ⟨ nat.add, tt ⟩ 

class inh_mul_twice (A : Type) extends inh_mul1 A, inh_mul2 A := (s : string)
instance inh_mul_twice_nat : inh_mul_twice nat := ⟨ nat.mul, 5, ff, "Hi" ⟩ 

instance inh_mul_twice_nat2 : inh_mul_twice nat := ⟨ inh_mul2.mul, 5, ff, "Hi" ⟩ 
