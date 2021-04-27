def list_map {α β : Type} : (α → β) → (list α) → list β 
| f list.nil := list.nil
| f (h::t) := (f h)::(list_map f t)

