/-
© 2021 by the Rector and Visitors of the University of Virginia
-/

import .lin2kcoord

/-
We illustrate the use of, and test, lin2kcoord.lean. 
-/

-- 2D coordinate vectors over a field, K = ℚ 
def v1 := ((1, 1) : ℚ × ℚ)
def v2 := ((-1,1) : ℚ × ℚ)

-- element addition, abstract now
def v3 := v1 + v2

example : v3 = (0,2) := 
begin
unfold v1 v2 v3,
simp,
trivial,
end

-- scaling (smul)
def v4 := 5 • v3
example : v4 = (0,10) := 
begin
  unfold v4 v3 v2 v1,
  simp,
  trivial,
end
