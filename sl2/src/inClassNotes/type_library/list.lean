namespace hidden

universe u

inductive list (α : Type u) : Type u
| nil {} : list
| cons (h : α) (t : list) : list

#check list
#check list nat
#check list string
#check list bool 

def l : list nat := list.nil
def t : list nat :=
  list.cons
    (3)
    (list.cons
      (4)
      (list.cons 
        5
        list.nil)
    )

#check (list.cons 5 list.nil)
-- [3,4,5]

/-
inductive list (α : Type u) : Type u
| nil {} : list
| cons (h : α) (t : list) : list
-/

def list_len {α : Type u} : list α → nat
| list.nil := 0
| (list.cons h t) := (list_len t) + 1

#eval list_len t

#print list

end hidden