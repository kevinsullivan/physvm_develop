/-
Higher-order, universe-agnostic 
function composition function. In
Lean this function is defined as
function.comp. It can be applied
using the infix notation, ∘, as
in the expression (g ∘ f), which
would be a function that first
applies f to its argument,  then
applies g to the result, finally
returning that resulting value. 
-/

universes u₁ u₂ u₃

def comp 
  {α : Type u₁} 
  {β : Type u₂} 
  {φ : Type u₃}  
  (g : β → φ) 
  (f: α → β) : 
  α → φ :=
fun a, g (f a)