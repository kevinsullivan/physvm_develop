import .uunit
import .space_standard

/-
Duplicated redundant code, see point1.
-/
universes u --v w
variables 
{K : Type u} [ring K] [inhabited K] 
{α : Type u} [has_add α]

/-
Build me a 2-d affine space from 2 1-d spaces, done
in a way that generalizes to higher dimensions, where

(0) the new space is built from  the component spaces
(1) the frame is built from from the component frames
(2) component elements are explicit in these composites
(3) provides a nice affine space "API" 
    - point 
    - vectr
    - frame 
    - space

Whether we use product types or findexing to represent
products is an open question at this point. It might be
worth exploring both. The one I'm best equipped to look
at is using product types. Charlie C., if you want to try
replacing products with findices, give it a go. We'll go
with whatever works out best.
-/

/-
INTRODUCE DIRECT SUM SPACE TYPE HERE
-- dependently typed n-tuple of subspaces
-- finitely indexed collection of subspaces
-/


/-
Standard space: 1-d affine with standard frame
-/
def std_space : spc (@std_fm K _ _) := mk_space std_fm

/-
One values for points and vectrs 
-/
def point_one := mk_point std_space (1:K) 
def vectr_one := mk_vectr std_space (1:K) 

/-
Zero values for points and vectrs 
-/
def point_zero := mk_point std_space (0:K) 
def vectr_zero := mk_vectr std_space (0:K) 

/-
Standard point, vector, frame, space
-/
def std_point := mk_point std_space (0:K) 
def std_vectr := mk_vectr std_space (1:K)
def std_frame : @fm K _ _ := mk_frame std_point std_vectr 
def std_space := mk_space (@std_frame K _ _) 
