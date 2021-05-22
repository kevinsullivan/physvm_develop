import .lin2kcoord

abbreviation K := ℚ 

-- two-D vectors over a field, K
def v1 := ((1, 1) : K × K)
def v2 := ((-1,1) : K × K)

-- translation (add)
def v3 := v1 + v2

-- scaling (smul)
def v4 := 5 • v3

-- test
#eval v4          -- expect (0,10)

-- accessors
#check v3.1 
#reduce v3.1      -- {num := int.of_nat 0, denom := 1, pos := _, cop := _}
#check v3.2 
#reduce v3.2      -- deterministic timeout

-- transformations
-- ?
