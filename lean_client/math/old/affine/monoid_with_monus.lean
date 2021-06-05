import algebra.group.basic


instance : add_semigroup ℕ := ⟨has_add.add, nat.add_assoc⟩
instance : add_monoid ℕ := ⟨has_add.add, nat.add_assoc, nat.zero, nat.zero_add, nat.add_zero⟩
instance : add_comm_semigroup ℕ := ⟨has_add.add, nat.add_assoc, nat.add_comm⟩
instance : add_comm_monoid ℕ := ⟨has_add.add, nat.add_assoc, nat.zero, nat.zero_add, nat.add_zero, nat.add_comm⟩

#eval (2 : ℕ) - (3 : ℕ)

#check nat.sub
