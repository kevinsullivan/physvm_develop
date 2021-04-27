/-
Eq
-/

#check @eq  -- binary relation : α → α → α 


#print eq
/-
inductive eq : Π {α : Sort u}, α → α → Prop
constructors:
eq.refl : ∀ {α : Sort u} (a : α), a = a
-/

/- 
Properties 
-/
#print eq

/-
-- reflexive    -- constructor
-- symmetric    <- reflexive
-- transitive   <- reflexive
-- equivalence  <- resymtr
-/


/-
AXIOMS
-/

/-
refl: Every thing equals itself
-/
#check @eq.refl 
/-
eq.refl: from any a, proof of a = a
-/
-- the only eq constructor
-- the one introduction rule

-- the one elimination rule
-- substitution of equals
/-
      subst 

        C : α → Prop
      /   \
    /       \
C a   >a=b>   C b

-/

#check @eq.rec

-- What does this type say?

/-
eq.rec : 
  Π {α : Sort u_2} 
    {a : α} 
    {C : α → Sort u_1}, 
    C a → 
    Π {ᾰ : α}, 
    a = ᾰ → 
    C ᾰ
-/

/-
For any type of object, α, 
for any a of this type,
and for any property, C α, of objects of type α, 
If you know or assume that a has property C
then for any other object, ᾰ, of type α 
if you know or assume that a and ᾰ are equal
then you may conclude that ᾰ also has that proeprty, C. 
So, if you need to prove C b it suffices to show C a and a = b.
Subst uses an equality a = b in order to rewrite a term C a to C b.
-/

/-
Prove that symmetry and transitivty are now theorems
-/

#check @eq.symm 

example : ∀ {α : Type } {a b : α}, a = b ↔ b = a :=  
begin
  assume α a b, 
  split,
  assume h,
  rw h,
  assume h,
  rw h,
end

example : ∀ {α : Type } {a b : α}, a = b ↔ b = a :=  
λ α a b, 
  (iff.intro 
    (λ aeqb, 
      (
        let s := eq.symm aeqb 
        in eq.subst aeqb (eq.refl a) 
      )
    )  
    (_)                 -- exercise!
  )


#check @eq.trans        -- exercise


-- tactic script
example : ∀ {α : Type } {a b c : α}, a = b → b = c → a = c := 
_


-- Lean term
example : ∀ {α : Type } {a b c : α}, a = b → b = c → a = c := 
_