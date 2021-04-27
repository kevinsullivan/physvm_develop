namespace hidden

/-
The "sum" type is used to hold either
a value of a type, α, or a value of 
another type, β. A value of the sum
type is often used to represent either 
a correct value or an error value (e.g.,
an error string or error code. Note: in
Haskell this type is called Either.
-/

inductive sum (α β : Type) : Type
| inl (a : α) : sum
| inr (b : β) : sum 

/-
Exercise: define a function, t2z, that 
takes a boolean argument, b. If b is tt, 
t2z returns the natural number, 0. If b
is not tt, the function returns an error
string, "Oops, argument not true."
-/

end hidden