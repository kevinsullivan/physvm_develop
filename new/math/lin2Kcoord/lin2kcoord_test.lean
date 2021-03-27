import .lin2kcoord

abbreviation K := ℚ 

def v1 : K × K := (1, 1)
def v2 : K × K := (-1,1)
def v3 : K × K := v1 + v2
def v4 := 5 • v3  -- expect (0,10)
#eval v4          -- confirmed