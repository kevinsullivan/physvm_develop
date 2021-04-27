
universes u₁ u₂ u₃ 

/-
The foldr function reduces a list α to a 
β value by applying a reducer function f
to (1) the (list head : α), and (2) the 
(result : β) of reducing the rest of the 
list to a result. 
-/
def foldr 
  {α : Type u₁} 
  {β : Type u₂} 
  :
  β →             
  (α → β → β) →       
  (list α → β)
| b f list.nil := b
| b f (h::t) := f h (foldr b f t) -- combine list head and reduction of rest

/-
The foldr function below takes a reducer
function as an argument. The function we
are currently considering, mk_reducer, 
builds these reducer functions from easy
to understand parts: (1) a function that
will convert the list head to a value that
will then be combined by (2) a function
that combines the converted value from the 
list head with the answer for the rest of
the list.
-/
def mk_reducer'
{α : Type u₁} 
{β : Type u₂} :
(α → β) →       -- list head converter
(β → β → β) →   -- results combiner
(α → β → β)     -- reducer function
| h r := λ b, r (h b)

/-
Note that this version of mk_reducer
is unnecessarily constrained. The only
fixed constraint is that the function
return a function (f : α → β → β). We
can do with less than (conv : α → β)
and (comb : β → β → β). In particular,
we can let conv output to a third type,
φ, as long as comb combines a value of
this type with the result of reducing
the rest of the list, yielding a value
of type β.
-/

def mk_reducer 
{α : Type u₁} 
{β : Type u₂} 
{φ : Type u₃} :
(α → φ) → (φ → β → β) → (α → β → β)
| conv comb := λ b, comb (conv b)

/-
From this analysis I reach the conclusion
that the "API" provided by foldr as we've
defined it here, that it hides power; that
a better API would let us plug in our own
values for conv and comb directly, rather
than having to pass a "reducer" function
that pre-composes conv and comb functions.
-/

def foldrx 
  {α : Type u₁} 
  {β : Type u₂} 
  {φ : Type u₃} :
  β → (α → φ) → (φ → β → β) → list α → β
| i v b [] := i
| i v b (h::t) := b (v h) (foldrx i v b t)

/-
β → 
(α → φ) → 
(φ → β → β) → 
list α → 
β
-/

-- That's T-shirt material right there