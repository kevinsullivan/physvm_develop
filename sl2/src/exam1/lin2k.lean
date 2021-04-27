import algebra.module.basic

/-
This is EXAM #1 for UVa CS 4501/6501, Spring
2021. 

Ground rules are as follows:
- open book, notes, code, WWW
- no communication except with instructors
- don't post any part of an answer on Piazza
- use Piazza only to ask about errors or to request clarifications

The exam is due before midnight on Friday, Apr 2.

Read the following and follow the instructions. 
Submit your completed lin2K_test.lean file. That's it!B
-/

/-
There are at least two important advantages
of defining a typeclass instance for a given
algebraic structure. First, if you actually
write the proofs, then you can be sure you
have made no mistakes. Second, in practical
terms, you also get a well organized set of
operations that allow you to "program in the
algebra." 

This problem will evaluate your ability to 
read and understand typeclass definitions 
and instances. In particular, we will build
an instsance of the Lean-give "vector_space"
typeclass to enable programming in a 2-D
vector space over any field K. Vectors will
be pairs of K values. Scalars will be single
K values. The two key operations are vector
vector addition and scalar multiplication of
a vector. 

More explanation follows, especially for
those students who've not had any linear
algebra. Don't worry, it's pretty easy.
-/

/-
We'll start by assuming that K is a non-empty
field.
-/

universes u 
variables {K : Type u} [field K] [inhabited K]

/-
Here's the typeclass we're going to instantiate.
The two type arguments, K and K × K, specify the
types of the scalars (K) and vectors (pairs of K
values). 
-/
#check vector_space K (K × K)

/-
Again, scalars of the vector space will 
be values of type K; while the vectors
will be pairs of scalar values. We will
also have vector-vector addition and
scalar-vector multiplication defined
"as usual": 

(k11,k12)+(k21,k22) = (k11+k21, k12+k22) 
k • (k11,k12) =(k * k11, k * k12) The +
notation between two vectors is overloaded
to mean vector addition as we've defined
it here. The + operator between two scalars
is addition in the scalar field. The • is 
infix for scalar vector multiplication
(smul). The * operator is multiplication
of scalars in the scalar field. 
-/

/-
In a nutshell, then, this module lets 
you write "2-D vector space code over
any field, K" with the standard vector 
space operators of vector-vector add
and scalar vector multiplication along
with the addition and multiplication of
scalars themselves.  
-/

/-
At this point the best way to understand what
follows is to jump to the end, see where we're 
going, read the associated comments, and work
backwards. You can actually skip ths step on a
first readings and just use the vector-space 
API that this module provides. 

We are not asking you to write typeclasses and
instances on this question. Your real focus 
should be on understanding (1) that creating a
typeclass instances let's you "write good code
in a given algebraic structure," (2) each of
the properties that the vector space and field
operators have to have to really have a vector
space.

Once you've understood what's in this file,
please go to the lin2k_test.file, and answer
the questions there.
-/

/-
Now please JUMP to the end of this file (look 
for "JUMP"). That's where we instantiate the
vector-space API for ordered pairs of field
values with the usual addition and scaling
operations. From there you will see what we
had to build by way of operations, "helper"
instances, and proofs (all stubbed out using
sorry), in order to create the vector_space
instance for values of type K and K × K. Work
your way back up to the comment just below
and you will have finished understanding what
we've done. Then go over to lin2k_test.lean
to answer the test questions.
-/

/-
Your UPWAWRD reading has now ended, too.
-/

/-
Ordered pair addition is already overloaded 
for values of type prod α β, courtesy of the
Lean library, provided that α and β themselves
have overloaded add (+) operations. The + 
notation is Lean-provided for *any* type that
implements has-add. Here we use it to add 
vectors in the form ordered pairs of K values.

Here is what it says in the Lean library. You
can always right click on a name and select
"go to definition" to see its definition. Try
it for has_add below. Here's what you'll find.

class has_add (α : Type u) := (add : α → α → α)
...
infix +        := has_add.add 

That's the class definition *and* the + notation.
-/
#check has_add  -- right click, go to definition

/-
In addition to vector-vector addition, a 
vector space also has a scalar-vector 
multiplication operator. Lean defines • 
as an infix notation for multiplying a 
scalar by a vector (scalar on left). So,
for example, if 5 is a scalar and (2, 3)
is a vector, you can write 5 • (2, 3) to
express the "scaling" of (2, 3) by 5. 

Here are details from the Lean library.
/-- Scalar multiplication operation, denoted `•` (`\bu`) -/
class has_scalar (α : Type u) (γ : Type v) := (smul : α → γ → γ)
infixr ` • `:73 := has_scalar.smul
-/
def scalar_vector_mul : K → K × K → K × K
| a (f,s) := ⟨ a * f, a * s ⟩ 

-- For our scalars smul will be our smul
instance : has_scalar K (K × K) := ⟨ scalar_vector_mul ⟩ 


/-
Rules for scalar multiplication.
- scalar multiplication by one
- scalar multiplication by produt of scalars

class mul_action (α : Type u) (β : Type v) [monoid α] extends has_scalar α β :=
(one_smul : ∀ b : β, (1 : α) • b = b)
(mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b)
-/
lemma one_smul_l2 : ∀ v : K × K, (1 : K) • v = v := sorry
lemma mul_smul_l2 : ∀ (x y : K) (b : K × K), (x * y) • b = x • y • b := sorry
instance : mul_action K (K × K) := ⟨ one_smul_l2, mul_smul_l2 ⟩ 


/-
Rules for scalar multiplication:
- multiplying scalar by sum of vectors
- multiplying scalar by zero vector

class distrib_mul_action (α : Type u) (β : Type v) [monoid α] [add_monoid β]
  extends mul_action α β :=
(smul_add : ∀(r : α) (x y : β), r • (x + y) = r • x + r • y)
(smul_zero : ∀(r : α), r • (0 : β) = 0)
-/
lemma smul_add_l2 : ∀ (r : K) (x y : K × K), r • (x + y) = r • x + r • y := sorry
lemma smul_zero_l2 : ∀ (r : K), r • (0 : K × K) = 0 := sorry
instance : distrib_mul_action K (K × K) := ⟨ smul_add_l2, smul_zero_l2⟩ 


/-
- scalar multiplication by a sum of scalars
- scalar multiplication by scalar zero

class semimodule (R : Type u) (M : Type v) [semiring R]
  [add_comm_monoid M] extends distrib_mul_action R M :=
(add_smul : ∀(r s : R) (x : M), (r + s) • x = r • x + s • x)
(zero_smul : ∀x : M, (0 : R) • x = 0)

Note that because K (R here) is assumed to be a field 
(see the top of this file), it is already equipped with 
a semiring and an additive monoid structure, so we don't
need to specify those ourselves. They're already "there."
-/
lemma add_smul_l2 : ∀ (r s : K) (x : K × K), (r + s) • x = r • x + s • x := sorry
lemma zero_smul_l2 : ∀ (x : K × K), (0 : K) • x = 0 := sorry
instance semimodule_K_Kpair : semimodule K (K × K) := ⟨ add_smul_l2, zero_smul_l2 ⟩ 


/-
Hi! JUMP down to here from above.
-/
/-
Instantiating the vector_space API for scalars of type
K and vectors of type K × K will provide us with nice
notations for writing typechecked algebraic expressions
in this space. For examples, see linear2K_test.lean. To
see what was required to instantiate this API/typeclass, 
see the comments below the live Lean code. They unpack
the definition of the vector_space typeclass from the
lean algebra library, revealing the prerequisites for
completing the job here. As you drill recursively down
through lower-level abstractions, you'll encounter new
algebraic structure names (things like "semimodule"). 
Now you have a good sense of what each of these classes
looks like: maybe some new data or operations, maybe
some new structuring constraints/rules/invariants.
-/
instance : vector_space K (K × K) := semimodule_K_Kpair
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
Yeah! We've now specified that we can treat 
ordered pairs over a field K a vector space,
with the following operations.

+   vector vector addition
•   scalar vector multiplication

Now proceed to linear2K_test.lean to show that 
you understand how to use this algebraic structure.
-/