universes u₁ u₂ 

structure box (α : Type u₁) : Type u₁ :=
mk :: (val : α)


def map_box 
  {α : Type u₁} 
  {β : Type u₂}
  (f : α → β)
  (b : box α) :
  box β := 
box.mk (f b.val) 
