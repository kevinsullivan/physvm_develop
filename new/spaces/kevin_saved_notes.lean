

/-
IGNORE KEVIN'S OLDER STUFF BELOW
-/

/-
structure dimension {f : @fm K _ _} (s : spc f) :=
mk ::

#check dimension
#check dimension std_spc

def prod_space : list (Σ f : (@fm K _ _), (@spc K _ _ f )) → Type u
| list.nil := uunit
| (⟨ fr,sp⟩ ::t) := prod (@dimension K _ _ fr sp) (prod_space t)/-std_spc-/ 
                                  -- ^^parameters^^^
-/

/- 
Instead of nat, take list/tree/etc of frames? 
STUCK
Not frames but (Σ f : (@fm K _ _), (@spc K _ _ f )) 
MAYBE? 
-/

