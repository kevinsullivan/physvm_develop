import .has_one

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
instance has_one_bool : hidden.has_one bool := 
⟨tt⟩   -- sorry, we just assume that proofs are given

/-
Note Lean provides has_one, so we have to use hidden.has_one
to get the version defined in our local namespace here. Oterwise
you get an ambiguous overload error message.
-/

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
def getMeABool [b : hidden.has_one bool] := b.one


