import ..type_library.box

namespace hidden

-- concrete example
def map_box_nat_nat 
  (f : nat → nat)
  (b : box nat) :
  box nat :=
  box.mk (f (b.val))

def box_inc := map_box_nat_nat (nat.succ)
#check box_inc 

#reduce box_inc (box.mk 5)
-- almost the most general case

universes u₁ u₂

def map_box 
  {α : Type u₁} 
  {β : Type u₂}
  (f : α → β)
  (b : box α) :
  box β := 
box.mk (f b.val) 

-- exercise: make it work for logical types

/-
On the following two assumptions, 
what is the type of (map_box f b)?
-/
variables 
  (f : string → nat)
  (b : box string)


def nbox := 
map_box 
  (λ s, s+1)
  (box.mk 5)

#reduce nbox  -- expected result???

end hidden
