#check 1



universes u v w

variables (p q : Prop)
variable  (α : Type u)
variable  (β : Type v)
variable  (γ : α → Type w)
variable  (η : α → β → Type w)

constants δ ε : Type u
constants cnst : δ
constant  f : δ → ε

variables (a : α) (b : β) (c : γ a) (d : δ)

variable  g  : α → β
variable  h  : Π x : α, γ x
variable  h' : Π x, γ x → δ

#check Sort (u + 3)
#check Prop
#check Π x : α, γ x
#check f cnst
#check λ x, h x
#check λ x, h' x (h x)
#check (λ x, h x) a
#check λ _ : ℕ, 5
#check let x := a in h x

#check Π x y, η x y
#check Π (x : α) (y : β), η x y
#check λ x y, η x y
#check λ (x : α) (y : β), η x y
#check let x := a, y := b in η x y

#check (5 : ℕ)
#check (5 : (λ x, x) ℕ)
#check (5 : ℤ)