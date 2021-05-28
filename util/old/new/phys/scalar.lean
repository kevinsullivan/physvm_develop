import ..math.aff1Kcoord.aff1Kcoord_std

--configure field here
abbreviation scalar := ℚ

/-
enforce constraint here 
(and up the stack - but to make it immediately clear when you do something bad)
-/
instance : inhabited scalar := by apply_instance
instance : field scalar := by apply_instance