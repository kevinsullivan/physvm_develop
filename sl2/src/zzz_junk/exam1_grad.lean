import algebra.module.basic

universes u 


/-
A vector space combines a set of scalar
values and a set of vector objects. In
a Lean formalization, these sets will be
represented by two types (called R and M
in Lean's library). The set of scalars 
must be a field, which means you have all
of the usual operations and properties of
arithmetic for scalars; and the set of
vectors must be an additive, commutative
group, so you can add scalars but there
is no operation for multiplying them. In
a vector space you can also multiply a
scalar by a vector, to "scale" it. 

To test your understanding and ability
to apply concepts we've studied in class
and on homeworks, you will show that a
pair of types and operations on them do
form a vector space.

To this end, you will assume that K is a
non-empty field, it doesn't matter what. 
K (R in the Lean libraries) is the scalar
field for your vector space, 
-/

variables (K : Type u) [field K] [inhabited K]

/-
The vectors, on the other hand, are ordered 
pairs of values of type K, i.e., values of
type K ⨯ K (i.e., prod K K).
-/

/-

Before going any further, try to convince
yourself completely informally that the pair
of types, K (K × K), forms a vector space
with the scalars being K objects, vectors 
being pair-of-K objects, you add ordered
pairs component-wise, multiplying a scalar
by a vector (pair) scales each of its two
components. Is it now true, for example, 
that adding two scalars (a + b) and then
multiplying that by a vector, v, is the
same as adding a times v and b times v?
Try it using the real numbers for K. Good.
-/


/-
Operations: add, scale, 
-/

def add : K × K → K × K → K × K
| (f1,s1) (f2,s2) := ⟨ f1 + f2, s1 + s2 ⟩ 

def scale : K → K × K → K × K
| a (f,s) := ⟨ a * f, a * s ⟩ 



-- delete
def negate : K × K → K × K
| (f,s) := ⟨ -1 * f, -1 * s ⟩ 

def sub :  K × K → K × K → K × K
| l1 l2 := add K l1 (negate K l2) 
--endelete


/-
You exam task is to instantate the
vector_space typeclass for the types
K and K ⨯ K. Doing this will certify
that you really do have a mathematical
vector space (except you will stub out
the proofs for now), and will provide
the benefits of Lean-library-defined
notations when subsequently writing 
code involving vector spaces. 
-/

/-
To get you started, you will now be
guided through the first few steps
of the process. Follow directions as
you proceed through the code below.
They ask you to jump around a bit 
so that (1) you see things in an 
order that makes sense, and (2) Lean
sees the in the order it needs to
compile the code.
-/


/-
Task: produce a "vector_space K (K × K)" instance.
-/
instance : vector_space K (K × K) :=
_
/-
Move this line of code to come after all of the
prerequisites, once they are built, below. We put
it here at the top so that you can see the main goal
up front: build an instance, vector_space K (K × K), 
of the vector_space typeclass. Read on.
-/

-- hover on "vector_space" for info from mathlib
#check vector_space K (K × K)
/-
A vector space is the same as a module, except 
the scalar ring is actually a field. (This adds 
commutativity of the multiplication and existence 
of inverses.) This is the traditional generalization 
of spaces like ℝ^n, which have a natural addition 
operation and a way to multiply them by real numbers, 
but no multiplication operation between vectors.
-/
/-
Don't gloss over the definitions. They are the keys.
Go see the definition in the Lean library. Read it!
It says that vector_space K (K ⨯ K) is really just
abbreviation for semimodule R M. 
-/
/-
vector_space : 
  Π (R : Type u_1)                -- ring of scalars
    (M : Type u_2)                -- set of vectoids
    [_inst_1 : field R]           -- implicit
    [_inst_2 : add_comm_group M], -- implicit
  Type (max u_1 u_2) :=
    semimodule R M      -- a vector space R M is a semimodule R M
-/



/-
Please jump directly to "semimodule" below. You will be
directed to return to this point further on.
-/
instance : distrib_mul_action K (K × K) := _
/-
distrib_mul_action : 
  Π (α : Type u) 
    (β : Type v) 
    [_inst_1 : monoid α] 
    [_inst_2 : add_monoid β], 
  Type (max u v)
-/
_

/-
Semimodule
-/
#check semimodule
/-
What we need is a "semimodule K (K × K) instance!"
To get that, we have to figure out what we need.
To do this, go look at the semimodule definition. 
-/
/- 
class semimodule (R : Type u) (M : Type v) [semiring R]
  [add_comm_monoid M] extends distrib_mul_action R M :=
(add_smul : ∀(r s : R) (x : M), (r + s) • x = r • x + s • x)
(zero_smul : ∀x : M, (0 : R) • x = 0)
-/
/-
It tells us that to create a semimodule instance we'll 
need instances of semiring K, add_comm_monoid K×K, and
distrib_mul_action K (K⨯L), and we'll need to provide
new operations and/or rules.
-/
/-
NB on NOTATION: In addition to abstract syntax, the Lean
libraries define infix notations. What this means is that
instance of writing "mul", for example, you can use * to
denote "multiplication as defined for a given structure." 
You will see notation in the statements of the properties
of a semimodule + means add in the given field, and the •
means "smul", an operation that needs to be provided, for
multiplying (scaling) a vector by a scalar on the left.
-/
instance : semimodule K (K × K) :=  
⟨ _, _ ⟩ 
/-
failed to synthesize type class instance for
K : Type u,
_inst_1 : field K,
_inst_2 : inhabited K
⊢ distrib_mul_action K (K × K)
-/
/-
Now go back and see the distrib_mul_action helper,
analyze what's missing there, provide the missing
pieces recursively until you're you're done. 

Reminder: You can jump into the Lean library to
see exactly how anything there is defined. Just
right click and select go to definition. You can
also hover over missing values or select them and
look in the Lean Info View to find out more about
what's missing and needed at a particular point.
-/
