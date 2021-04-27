namespace hidden

universe u

inductive sum (α β : Type u) : Type u
| inl (a : α) : sum
| inr (b : β) : sum 

end hidden

#check sum nat Type