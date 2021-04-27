
def id_nat : nat → nat :=
  λ n, n 

def id_string : string → string :=
  λ n, n 
  
def id_bool : bool → bool :=
  λ n, n 

-- parametric polymorphism

namespace hidden 

#check 1
#check "Hello"
#check tt

-- Types are terms 

#check nat 
#check string
#check bool

def id' : Π (α : Type), α → α := 
  λ α,
    λ n,
      n

#eval id' bool tt
#eval id' string "Hello, Lean!"
#eval id' nat 5

-- Type inference 
#eval id' _ tt
#eval id' _ "Hello, Lean!"
#eval id' _ 5

-- implicit type inference

universe u

def id : Π { α : Type u}, α → α := 
λ α, 
  fun a, 
    a
/-
  λ α,
    λ n,
      n
-/

#eval id tt
#eval id "Hello, Lean!"
#eval id 5

-- error cases
#eval id _         -- can't infer α 
#eval id nat _     -- type error!

-- turn off implicit typing
#eval (@id nat) _   -- all goot, expects ℕ 

#check 1
#check nat 
#check Type 
#check Type 1

#reduce (id nat)


end hidden 

#check hidden.id