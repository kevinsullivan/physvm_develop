inductive Syntax : Type
| I
| II
| III
| IV
| V

inductive Semantics : Type
| one
| two
| three
| four
| five


#reduce Semantics.one -- Qualified access to that namespace

open Semantics        -- Open namespaces

open Syntax

#reduce one           -- Now defined in current namespace

/-
Here's an informal definition of
our desired semantics.

I   -->   one
II  -->   two
III -->   three
IV  -->   four
V   -->   five
-/

-- We can formalize semantics as a function

/-
A little bit of Lean
-/

-- Literal expressions
-- Variable expressions
-- Application expressions

#reduce 1   -- literal

def x := 1  -- variable
#reduce x

def my_id : nat → nat := (λ n, n)   -- lambda expression, literal
--  Ident   Type         Value
                                    -- type inference in use

#reduce (my_id 1)
#reduce (my_id 4)
-- #reduce (my_id "Hello, Lean!")

def my_id' : ℕ → ℕ  -- by cases
| n := n

def my_id'' (n : nat) : nat :=    -- C style syntax
n

#reduce my_id
#reduce my_id''

-- End of "A little bit of Lean"

-- Another aside

def my_add (n m : ℕ) := nat.add n m  -- n + m

#reduce my_add 2 3

def my_add' : ℕ → (ℕ → ℕ) := 
  λ n,
    λ m, 
      n + m

def k := my_add' 5

#reduce k 6

/-
Our semantics!
-/

def my_eval : Syntax → Semantics 
| I := one 
| II := two
| III := three
| IV := four
| V := five

#reduce my_eval II 

-- computational: def c_semantics_fun  : input -> c-program -> output
-- logical:       def c_semantics_pred : input -> c-program -> output -> Prop