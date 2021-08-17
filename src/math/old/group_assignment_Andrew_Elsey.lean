import data.real.basic 
import algebra.group
import algebra.group.basic
import group_theory.order_of_element

--def a [group (fin 4)] := fin 4
--def b [group (fin 2)] := fin 2

--def c : a := 2

--#check order_of c

--abbreviation a := fin 4
--abbreviation b := fin 2

/-
Here, courtesy of a colleague posting on the open internet, 
is a nice written introduction to go along with the video:
 http://facstaff.cbu.edu/wschrein/media/M402%20Notes/M402C1.pdf. 
 Among other things, it contains the "multiplication table" (Cayley table) for
  actions in the group of symmetries of a square. I would like everyone to read 
  it along with watching the video. As an extra exercise, required of graduate students,
   extra credit for undergraduates, define a type and a function to implement this group in Lean. 
   It's easy. The eight values of the type will represent the eight symmetries of the square. 
   For constructor names, you might want to use names like those in the linked notes. 
   With your type in hand, define a function, comp (for "compose actions"),
    that takes two "action" values  and return the result as defined by the multiplication table.  
    Use foldr to implement a function, comp_list, that takes a list of actions and reduces it to the 
    single action that is the result of composing all of the actions in the list. You do not need, 
    and should not try, to use typeclasses for this exercise.

 
-/

/-
define a type and a function to implement this group in Lean. 
   It's easy. The eight values of the type will represent the eight symmetries of the square. 
   For constructor names, you might want to use names like those in the linked notes. 

   -- Is the V H style common? I'm using the a b which is likely familiar...
-/

inductive dihedral_group
| r0 : dihedral_group
| r90 : dihedral_group
| r180 : dihedral_group
| r270 : dihedral_group
| H : dihedral_group
| V : dihedral_group
| D : dihedral_group
| D' : dihedral_group

open dihedral_group

def comp : dihedral_group → dihedral_group → dihedral_group  
| (r0) (r0) := r0 | (r0) (r90) := r90 | (r0) (r180) := r180 | (r0) (r270) := r270 
    | (r0) (H) := H | (r0) (V) := V | (r0) (D) := D   | (r0) (D') := D'
| (r90) (r0) := r90 | (r90) (r90) := r180 | (r90) (r180) := r270 | (r90) (r270) := r0 
    | (r90) (H) := D' | (r90) (V) := D | (r90) (D) := H | (r90) (D') := V
| (r180) (r0) := r180 | (r180) (r90) := r270 | (r180) (r180) := r0 | (r180) (r270) := r90 
    | (r180) (H) := (V) | (r180) (V) := H | (r180) (D) := D' | (r180) (D') := D
| (r270) (r0) := r270 | (r270) (r90) := r0 | (r270) (r180) := r90 | (r270) (r270) := r180 
    | (r270) (H) := (D) | (r270) (V) := D' | (r270) (D) := V | (r270) (D') := H
| (H) (r0) := H | (H) (r90) := D | (H) (r180) := V | (H) (r270) := D' 
    | (H) (H) := r0 | (H) (V) := r180 | (H) (D) := r90 | (H) (D') := r270
| (V) (r0) := V | (V) (r90) := D' | (V) (r180) := H | (V) (r270) := D 
    | (V) (H) := r180 | (V) (V) := r0 | (V) (D) := r270 | (V) (D') := r90
| (D) (r0) := D | (D) (r90) := V | (D) (r180) := D' | (D) (r270) := H
    | (D) (H) := r270 | (D) (V) := r90 | (D) (D) := r0 | (D) (D') := r180
| (D') (r0) := D' | (D') (r90) := H | (D') (r180) := D | (D') (r270) := V
    | (D') (H) := r90 | (D') (V) := r270 | (D') (D) := r180 | (D') (D') := r0

def comp_list (ls : list dihedral_group) : dihedral_group :=
  list.foldr comp r0 ls


example : (comp_list [r0,r0,r0]) = r0 := rfl
example : (comp_list [r90,r90,r90]) = r270 := rfl 

inductive dihedral_group'
| e : dihedral_group'
| a : dihedral_group'
| aa : dihedral_group'
| aaa : dihedral_group'
| b : dihedral_group'
| ba : dihedral_group'
| baa : dihedral_group'
| baaa : dihedral_group'

/-With your type in hand, define a function, comp (for "compose actions"),
    that takes two "action" values  and return the result as defined by the multiplication table.  
-/
open dihedral_group'

def comp' : dihedral_group' → dihedral_group' → dihedral_group'  
| (e) (e) := e | (e) (a) := a | (e) (aa) := aa | (e) (aaa) := aaa 
    | (e) (b) := b | (e) (ba) := ba | (e) (baa) := baa   | (e) (baaa) := baaa
| (a) (e) := a | (a) (a) := aa | (a) (aa) := aaa | (a) (aaa) := e 
    | (a) (b) := baaa | (a) (ba) := b | (a) (baa) := ba | (a) (baaa) := baa
| (aa) (e) := aa | (aa) (a) := aaa | (aa) (aa) := e | (aa) (aaa) := a 
    | (aa) (b) := (baa) | (aa) (ba) := baaa | (aa) (baa) := b | (aa) (baaa) := ba
| (aaa) (e) := aaa | (aaa) (a) := e | (aaa) (aa) := a | (aaa) (aaa) := aa 
    | (aaa) (b) := (ba) | (aaa) (ba) := baa | (aaa) (baa) := baaa | (aaa) (baaa) := b
| (b) (e) := b | (b) (a) := ba | (b) (aa) := baa | (b) (aaa) := baaa 
    | (b) (b) := e | (b) (ba) := a | (b) (baa) := aa | (b) (baaa) := aaa
| (ba) (e) := ba | (ba) (a) := baa | (ba) (aa) := baaa | (ba) (aaa) := b 
    | (ba) (b) := aaa | (ba) (ba) := e | (ba) (baa) := a | (ba) (baaa) := aa
| (baa) (e) := baa | (baa) (a) := baaa | (baa) (aa) := b | (baa) (aaa) := ba
    | (baa) (b) := aa | (baa) (ba) := aaa | (baa) (baa) := e | (baa) (baaa) := a
| (baaa) (e) := baaa | (baaa) (a) := b | (baaa) (aa) := ba | (baaa) (aaa) := baa
    | (baaa) (b) := a | (baaa) (ba) := aa | (baaa) (baa) := aaa | (baaa) (baaa) := e
  
/-
Use foldr to implement a function, comp_list, that takes a list of actions and reduces it to the 
    single action that is the result of composing all of the actions in the list. You do not need, 
    and should not try, to use typeclasses for this exercise.

-/

def comp_list' (ls : list dihedral_group') : dihedral_group' :=
  list.foldr comp' e ls


example : (comp_list' [e,e,e]) = e := rfl
example : (comp_list' [ba,a,a]) = baaa := rfl