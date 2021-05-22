import linear_algebra.affine_space.affine_equiv

/-
5/17/21 

CANNOT REALLY DO THIS 

⊤ has no inverse

-/


#check set

abbreviation top_type := {x // x ∈ [0,1]}
--#check (⊤ : ℚ) 
--notation ⊤ := top_type

#check has_top

--#check (⊤ : ℚ) 

structure ℚ_Top := 
  (val : ℚ)
  (top : top_type)
  (is_top_or_Q : top.val=1 → val = 0)

def top : ℚ_Top := ⟨0, ⟨1, by simp *⟩, by simp *⟩

instance : has_top ℚ_Top := ⟨top⟩

instance is_top (qt : ℚ_Top): decidable (qt=⊤) := 
begin
  cases qt,
  cases qt_top,
  cases qt_top_val,
  cases ⊤,
  cases top,
  simp *,
  exact decidable.is_false (by cc) 
end

def ℚ_Top_add : ℚ_Top → ℚ_Top → ℚ_Top :=
  begin
    intros a b,
    cases b,
    cases (a=⊤ : bool),
  end

def pf : field ℚ_Top := 
  ⟨
    begin
      intros a b,
      
    end,
    begin
    end,
  ⟩

instance : field ℚ_Top := 
⟨

⟩

