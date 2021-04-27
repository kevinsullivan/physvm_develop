/- A FAMILY OF TYPES ("INDUCTIVE FAMILY")

efine a family of types, *tuple n*, indexed
by natural numbers. For any (n : nat), tuple n 
is the type of tuples (of natural numbers) of 
length n. 
-/


-- nat ⨯ nat

--  ℕ ℕ ℕ 
-- (1,2,3)

--  ℕ ⨯ (ℕ×ℕ) 
-- (1,(2,3))

-- (1, (2, (3, (4, 5))))

/-
Build a function that takes a natural number, n,
and returns a TYPE: the type of tuples of length
n.

#check tuple

nat → (nat ⨯ (nat ⨯ nat))

tuple : Π (n : ℕ), _
-/

/-
Reminder: prod is a type builder. Given
types, α and β, prod α β (or α × β) is the
the *type* of ordered α-β pairs. We can
then use prod.mk to create values of such
a type. 

The following function recursively applies
× to nat, enabling us to build product types
with any number of components, not just two
(where, here, for simplicity, we support
only products of the nat type). The base
case for the recursion when n=0 is the unit
type. 
-/

-- for each (n : nat), a type, (tuple n)
def tuple : nat → Type
| 0 := unit
| (n' + 1) := nat × (tuple n')

/-
0   tuple 0 = unit
1   tuple 1 = nat ⨯ unit
2   tuple 2 = nat ⨯ (nat ⨯ unit)
3   tuple 3 = nat ⨯ (nat ⨯ (nat ⨯ unit))
4   tuple 4 = nat ⨯ (tuple 3)
...
n   tuple (n' + 1) = nat ⨯ (tuple n')
-/

#check tuple  -- ℕ → Type (*important*)

#check nat
#check (prod nat nat)

/-
For values of n from 0 to 3, we get the 
following types by applying tuple to n.

0: unit
1: nat ⨯ unit
2: nat × (nat × unit)
3: nat × (nat × (nat × unit)) 

Values of these types include:

0 : (unit.star)
1: (1, unit.star)
2: (1, 2, unit.star)
3: (1, 2, 4, unit.star)
-/

def t0 : tuple 0 := unit.star
def t1' : tuple 1 := prod.mk 1 unit.star
def t1 : tuple 1 := (1, unit.star)  -- notation
def t2 : tuple 2 := (1, 2, unit.star)
def t3 : tuple 3 := (1, (2, (4, (unit.star))))

--  (1, 2, unit.star)
--  (1, (2, (unit.star)))
-- prod.mk 1 (prod.mk 2 unit.star)


/-
The length is typechecked! The error
messages are cryptic, but, hey.
-/

def t3' : tuple 3 := (1, 2, 3, 4, unit.star) -- no
def t3'' : tuple 3 := (1, 2, 4, unit.star) -- no

/-
We could define a nicer concrete syntax that 
would let us avoid having to write the star
at the end, but we'll skip that here to stay
focused on the essentials. 
-/

/-
Note that tuple is a *type builder*. It
takes a natural number, n, and returns a 
*type*: in particular, one that depends 
on n. Tuple is defined by recursion on n.
It iteratively computes the product type
of nat and smaller product of nats until
n=0, at which point it returns the product
of all that with the unit type (base case).
-/

/-
More generally, given (α : Type) and 
(β : α → Type), we can view β as defining
a *family of types over α*, with a different
type, (β a), for such each value, (a : α). 

In our example above, α = nat and β = tuple.
Tuple defines an inductive family of types
"indexed by the natural numbers." To each
natural number, n, tuple thus associates 
a corresponding type, tuple n,that depends
on n.
-/

def n0 : tuple 0 := ()
#reduce n0

def nil := tuple 0

def cons : Π {n : ℕ}, nat → tuple n → tuple (n + 1) 
| n a t := prod.mk a t

-- {2} 7 (1, 2, star) -> (7, (1, 2, star))
-- #reduce cons 7 ((1, (2, unit.star)) : tuple 2)

def head : Π {n : nat}, tuple  n → option nat
| 0 _ := none
| (n' + 1) (prod.mk h t) := some h

def tail {α : Type} : Π (n : nat), tuple n → option (tuple (n-1))
| 0 _ := none
| (n' + 1) (prod.mk h t) := some t

def append :
  Π {n m : ℕ}, (tuple n) → tuple m → tuple (m + n)
| 0 m tn tm := tm
| (n' + 1) m (prod.mk h tn') tm := prod.mk h (append tn' tm) -- infers n' m

def t6 := append t3 t3
#reduce t6

-- Type check catches bounds errors
def foo (t : tuple 3) : nat := 0
#check foo t2   -- No: type of t2 is tuple 2, not tuple 3

/-
DEPENDENT FUNCTION TYPES
-/

/-
The importance of Pi types, Π x : α, β x, is that they generalize 
the notion of a function type, α → β, by allowing the type, β, to 
depend on  (a : α). Here's a function that takes a value, n, of
type nat, and that returns a value of type *(tuple n)*. Clearly
the type of the return value depends on the value of the argument,
n. It should now also be clear why Π binds a name to an argument:
so that the value can be used in defining the rest of the *type*
of a function.
-/
def zerotuple : Π (n : nat), tuple n
| 0 := ()
| (n' + 1) := (0, zerotuple n')


-- Π (n : nat), tuple n

#reduce zerotuple 4
#check zerotuple 4

def nToNtuple (n : nat) : tuple n := zerotuple n
#check nToNtuple

def z0 := nToNtuple 0
def z1 := nToNtuple 1
def z2 := nToNtuple 2
def z3 := nToNtuple 3
def z4 := nToNtuple 4

#check z0
#check z1
#check z2
#check z3
#check z4

#reduce z0
#reduce z1
#reduce z2
#reduce z3
#reduce z4

-- General notation for dependently typed functions
-- Π (a : A), B a 
-- Π (n : ℕ), tuple n

-- Π (a : A), B   -- special case where B doesn't depend on a 
-- A → B 


-- Ours is a dependently typed function
#check nToNtuple


/-
SIGMA (DEPENDENT PRODUCT) TYPES
-/

#print sigma

/-
structure sigma : Π {α : Type u}, (α → Type v) → Type (max u v)
fields:
sigma.fst : Π {α : Type u} {β : α → Type v}, sigma β → α
sigma.snd : Π {α : Type u} {β : α → Type v} (c : sigma β), β c.fstLean
-/

#check Σ (n : nat), tuple n   -- dependent pair type, ⟨ n, tuple n ⟩ 

def s3 : Σ (n : nat), tuple n := sigma.mk 3 (1,2,3,unit.star) 
def s5 : Σ (n : nat), tuple n := ⟨  5, (nToNtuple 5) ⟩ 
def sx : Σ (n : nat), tuple n := ⟨ 5, (nToNtuple 4) ⟩ -- Cannot form, snd has wrong type

#print sigma 

#reduce sigma.fst s3
#reduce sigma.snd s3
#reduce s3.fst
#reduce s3.snd
#reduce s3.1
#reduce s3.2

-- Identical types, varying in notation
#check Σ (n : nat), tuple n 
#check @sigma nat tuple

#check sigma.mk 3 (nToNtuple 3)
#check sigma.mk 4 (nToNtuple 4)
#reduce sigma.mk 3 (nToNtuple 3)
#reduce sigma.mk 4 (nToNtuple 4)



def nToSigma (n : nat) : sigma tuple := 
⟨ n, nToNtuple n⟩ 

def nToSigma' (n : nat): Σ (n : nat), tuple n :=
⟨ n, nToNtuple n⟩ 


#reduce nToSigma 5


/-
variable α : Type
variable β : α → Type
variable a : α
variable b : β a

#check sigma.mk a b      -- Σ (a : α), β a
#check (sigma.mk a b).1  -- α
#check (sigma.mk a b).2  -- β (sigma.fst (sigma.mk a b))

#reduce  (sigma.mk a b).1  -- a
#reduce  (sigma.mk a b).2  -- b-/

def evenNum : {n : nat // n%2 = 0} := ⟨ 2, rfl ⟩ 

#reduce evenNum

def oops : {n : nat // n%2 = 0} := ⟨ 3, rfl ⟩ 

def evenId : {n : nat // n%2 = 0} → nat 

| ⟨ val, proof_about_val ⟩ := val

#eval evenId ⟨ 0, rfl ⟩ 
#eval evenId ⟨ 1, rfl ⟩ 
#eval evenId ⟨ 2, rfl ⟩ 
#eval evenId ⟨ 3, rfl ⟩ 
#eval evenId ⟨ 4, rfl ⟩ 
#eval evenId ⟨ 5, rfl ⟩ 

#print subtype