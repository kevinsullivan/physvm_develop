-- for each (n : nat), a type, (tuple n)
def tuple : nat → Type
| 0 := unit
| (n' + 1) := nat × (tuple n')
