import ..algebra
/-
The group, D4.
-/

inductive dihedral_4 : Type
| r0     -- 0 quarter turns    r: rotation
| r1     -- 1 quarter turn
| r2     -- 2 quarter turns
| r3     -- 3 quarter turns
| sr0    -- flip horizontal   s: reflection
| sr1    -- flip ne/sw
| sr2    -- flip vertical
| sr3    -- flip nw/se

open dihedral_4

def e := r0

def mul : 
  dihedral_4 → dihedral_4 → dihedral_4  -- closed
| _ _ := r0 

/-
r^n is still a rotation
sr^n and r^ns are reflections
-/