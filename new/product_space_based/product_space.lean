import .uunit
import .point1

/-
Duplicated redundant code, see point1.
-/
universes u --v w
variables 
{K : Type u} [ring K] [inhabited K] 
{α : Type u} [has_add α]

/- 
BIG IMPORT. CHECK INTERFACES.

def std_frame : @fm K _ _ := mk_frame std_point std_vectr
def std_space := mk_space (@std_frame K _ _)

Incoming from point1 is a 1-d,
standard, K-affine space object, 
(std_space : spc std_frame), in 
turn built on spc, fm, etc. 
-/

/-
  Abstraction layer boundary
-/

#check std_frame    -- uses fm
#check std_space    -- hide spc

/-
And now d-dim product space type family. 

Not tuples of coordinates but of spaces.

Not exactly this:
def product_space : nat → Type
| 0 := unit
| (n' + 1) := space × (space_tuple n')

But this: Tuples of spaces.

But what is a "space"? It's the *type* of
std_space.

(std_space : spc std_frame)
-/

#check std_space
#check std_frame


structure dimension {f : @fm K _ _} (s : spc f) :=
mk ::

#check dimension
#check dimension std_spc

def prod_space : list (Σ f : (@fm K _ _), (@spc K _ _ f )) → Type u
| list.nil := uunit
| (⟨ fr,sp⟩ ::t) := prod (@dimension K _ _ fr sp) (prod_space t)/-std_spc-/ 
                                  -- ^^parameters^^^


/- 
Instead of nat, take list/tree/etc of frames? 
STUCK
Not frames but (Σ f : (@fm K _ _), (@spc K _ _ f )) 
MAYBE? 
-/