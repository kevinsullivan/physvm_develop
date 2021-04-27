import ..has_one.has_one

open hidden

/-
Use a typeclass instance to overload operator symbol
for a specific type. Each typeclass instance provides 
values for "its" associated type.
-/

/-
Create a single typeclass instance (structure). It 
gets registered into a database of such instsances.
-/
instance has_mul_bool : hidden.has_mul bool := ⟨ band ⟩ 
/-
This code would typically be co-located witht he code
that defines the bool type, because this instance 
defines what the operator returns when applied to the
type, bool. Instances implement overloaded operators
*for specific types*, and its the type definitions
themselves, that should provide define how each 
overloaded operator is implemented for that type. 



When needed, this structure can be fetched by means
of typeclass inferencing. Here we get back the bool
value stored as a identity for bool multiplication 
(which we take to be performed by band, by the way). 
-/

def my_band [b : hidden.has_mul bool] := b.mul

-- as expected ...
#check my_band
#eval my_band ff ff
#eval my_band ff tt
#eval my_band tt ff
#eval my_band tt tt

-- Yep, that's band alright


