#print option

namespace hidden

universe u 

inductive option (α : Type u) : Type u
| none {} : option
| some (a : α) : option

end hidden