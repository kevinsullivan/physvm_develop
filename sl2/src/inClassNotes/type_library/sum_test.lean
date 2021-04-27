/-
The "sum" type is used to hold either
a value of a type, α, or a value of 
another type, β. 

Here's the definition

universe u

inductive sum (α β : Type u) : Type u
| inl (a : α) : sum
| inr (b : β) : sum 

In Haskell this type builder is called Either.
-/

/-
Example #1

A value of a sum type can be used
as a more powerful option type, one
where either a correct value or an
argument-specific error is returned. 


-/

-- return either correct answer or error string
def pId (n : ℕ) : sum bool string :=
  if (n%2 = 0) 
  then sum.inl tt 
  else sum.inr ("pb2n is undefined for n = " ++ repr n)

#eval pId 0
#eval pId 1
#eval pId 2
#eval pId 3
#eval pId 4
#eval pId 5

def pIdIsDef (n : ℕ) : bool :=
let result := (pId n) in
  match (result) with
  | sum.inl _ := tt
  | _ := ff
  end 

-- predicate, tt if pId defined for n, else ff
#eval pIdIsDef 0
#eval pIdIsDef 1
#eval pIdIsDef 2
#eval pIdIsDef 3
#eval pIdIsDef 4
#eval pIdIsDef 5

/-
Example. Suppose we have a type of healthy food, 
fruit, and another type of healthy food, veggy.
-/

inductive fruit 
| apple
| orange
| kiwi

inductive veggy
| kale
| brocolli
| turnip

open fruit veggy

/-
How do we combine these types into one 
new type? Small portions are especially
healthy, so we don't want a pair of foods.
-/

-- product type

def p1 : prod fruit veggy := prod.mk apple kale
def p2 : fruit × veggy := (apple, kale)

/-
Rather, we want *either* a fruit or a veggy,
but only one of the two. Voila, the sum type.
-/
-- sum type

def healthy1 : sum fruit veggy := sum.inl apple
def healthy2 : fruit ⊕ veggy := sum.inr kale 


#check @sum.inl