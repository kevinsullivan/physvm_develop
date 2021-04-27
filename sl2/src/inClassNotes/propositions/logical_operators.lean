/-
When propositions are represented as types,
...
-/


/-
The proposition, false, is represented as 
a empty type. False is a proposition (type) 
with no proof (values). It's just like the
empty type we've already seen but it lives
in Sort 0 (Prop) rather than in any of the
Type universes. Again that has consequences
for proof irrelevance and universe levels.
-/

#check false  -- right click, go to definition

/-
The proposition, true, is represented as a
single-valued type, just like unit, but now
in Prop instead of in Type. The proposition,
true, is always trivally proven and carries
no real information content. knowing that 
it's true doesn't tell you anything useful
because it's always just true.  
-/

#check true       -- see Lean's definition
#check true.intro -- proof is always there


/-
and  : Prop → Prop → Prop
prod : Type → Type → Type
-/


/-
or      : Prop → Prop → Prop
either  : Type → Type → Type
-/


/-
implies :   Prop → Prop 
fun :       Type → Type
-/


/-
not :       Prop → Prop
-/



/-
exists :              
  ∃ (a : α), B a  
    {α : Type u}
    {β : α → Prop}

Σ ...
-/


axioms (α : Type) { β : α → Prop}

#check Σ (a : α), β a 


-- 

/-
The role of dependent types here is 
really essential: it's what allows a
proposition in effect to talk about an
assumed object introduced into scope.
-/

def true_intro : pExp := pTrue
def false_elim := pFalse >> P
def true_imp := pTrue >> P
def and_intro := P >> Q >> P ∧ Q
def and_elim_left := P ∧ Q >> P
def and_elim_right := P ∧ Q >> Q
def or_intro_left := P >> P ∨ Q
def or_intro_right := Q >> P ∨ Q
def or_elim := P ∨ Q >> (P >> R) >> (Q >> R) >> R
def iff_intro := (P >> Q) >> (Q >> P) >> (P ↔ Q)
def iff_intro' := (P >> Q) ∧ (Q >> P) >> (P ↔ Q)
def iff_elim_left := (P ↔ Q) >> (P >> Q)
def iff_elim_right := (P ↔ Q) >> (Q >> P)
def arrow_elim := (P >> Q) >> (P >> Q)
def resolution := (P ∨ Q) >> (¬ Q ∨ R) >> (P ∨ R)
def unit_resolution := (P ∨ Q) >> ((¬ Q) >> P)
def syllogism := (P >> Q) >> (Q >> R) >> (P >> R)
def modus_tollens := (P >> Q) >> (¬ Q >> ¬ P)
def neg_elim := (¬ ¬ P) >> P
def excluded_middle := P ∨ (¬ P)
def neg_intro := (P >> pFalse) >> (¬ P)

def affirm_consequence := (P >> Q) >> (Q >> P)
def affirm_disjunct := (P ∨ Q) >> (P >> ¬ Q)
def deny_antecedent := (P >> Q) >> (¬ P >> ¬ Q)
