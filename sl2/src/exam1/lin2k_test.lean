import data.real.basic
import .lin2k


-- Let's work with rational number field
abbreviation K := ℚ  

-- Here are nice abbreviations for types
abbreviation scalr := K
abbreviation vectr := K × K


#check ℝ 
/-
1A. [10 points]

Declare v1, v2, and v3 to be of type
vectr with values (4,6), (-6,2), and
(3, -7), respectively.
-/

-- HERE

def v1 : vectr := (4,6)
def v2 : vectr := (-6,2)
def v3 : vectr := (3,-7)

/-
1B. [10 points]

Now define v4, *using the vector 
space operators, + and •, to be 
the following "linear combination"
of vectors: twice v1 plus negative 
v2 plus v3. The negative of a vector
is just -1 (in the field K) times
the vector. Write -1 as (-1:K), as 
otherwise Lean will treat it as the 
integer -1. (Note that subtraction
of vectors, v2 - v1 is defined as
v2 + (-1:K) • v1.)
-/

-- HERE 

def v4 := 2*v1 + (-v2) + v3

/-
Compute the correct answer by hand
here, showing your work, and check
that eval is producing the correct
answer. 

-- HERE

2*v1 + (-v2) + v3 =
2*(4,6) + (-v2) + v3 = 
(8,12) + (-v2) + v3 =
(8,12) + (-(-6,2)) + v3 =
(8,12) + (6,-2) + v3 =
(14,10) + v3 = 
(14,10) + (3,-7) = 
(17,3)

-/

#eval v4

/-
1C. [10 points]

On a piece of paper, draw a picture
of the preceding computation. Make a
Cartesian plane with x and y axes. 
Draw each vector, v1, v2, v3, as an
arrow from the origin to the point
designated by the coordinates of the
vector.

Scalar multiplication stretches or
shrinks a vector by a given factor.
Show each of the scaled vectors in 
your picture: 2 • v1 and (-1:K) • v2. 

Finally vector addition in graphical
terms works by putting the tail (non
arrow) end of one vector at the head
of the other then drawing the vector
from the tail of the first to the head
of the second. Draw the vectors that
illustrate the sum, v1 + (-1:K) • v2,
and then the sum of that with v3. You
should come out with the same answer
as before. Take a picture of your
drawing and upload it with your test.
-/

-- HERE

/-
2. [15 points]

Many sets can be viewed as fields. For 
example, the integers mod p, where p is
any prime, has the structure of a field
under the usual operations of addition
and multiplication mod p.

In case you forget about the integers 
mod n, it can be understood as the set
of natural numbers from 0 to n-1, where
addition and multiplication wrap around.

For example, the integers mod 5 is the
set {0, 1, 2, 3, 4}. Now 2 + 2 = 4 but
2 + 3 = 5 = 0. It's "clock arithmetic," 
as they say. Similarly 2 * 2 = 4 but 
2 * 3 = 6 = 5 + 1 = 0 + 1 = 1. 

To show informally that the integers 
mod 5 is a field you have to show that
every element of the set has an additive
inverse and that every element of the 
set but 0 has a multiplicative inverse.

Draw two tables below with the values
of the integers mod 5 in each of the 
left column. In the second column of
the first table, write in the additive
inverses of each element. In the second
table, write the multiplicative inverses.
-/

-- HERE


/-
Z/5|ADD INVERSE|MUL INVERSE
0|0|NONE
1|4|1
2|3|2
3|2|3
4|1|4

-/

/-
4. [15 points]
Is the integers mod 4 a field? If so,
prove it informally by writing tables
giving the inverses. If not, show that
not every value in the integers mod 4
(except 0) has a multiplicative inverse,
identify a value that doesn't have an
inverse, and briefly explain why.
-/

-- HERE
/-
Z/4|ADD INVERSE|MUL INVERSE
0|0|NONE
1|3|1
2|2|?
3|1|3


IIRC n needs to be prime. As is evident, 2x2 = 0 (zero di...), but, assuming 2 did have a multiplicative inverse,
 2⁻¹(2x2=0) → 2 = 0 (i.e., False!)
-/

/-
5. [20 points]
Write a function, sum_vectrs, that 
takes a list of our vectr objects as 
an argument and that reduces it to a 
single vector sum. To implement your
function use a version of foldr as we
developed it: one that takes an additive
monoid implicit instance as an argument, 
ensuring consistency of the operator we
are using to reduce the list (add) and 
the corresponding identity element. 
Copy and if needed modify the foldr
definition here. It should use Lean's 
monoid class, as we've done throughout
this exercise. You do not need to and
should not try to use our algebra.lean 
file. Test your function by creating a
list of vectrs, [v1, v2, v3, v4], from
above, compute the expected sum, and
show that your function returns the 
expected/correct result.
-/

-- HERE
universes u
def mul_monoid_foldr 
  {α : Type u} 
  [monoid α] 
  :
  list α → α 
| [] := has_one.one
| (h::t) := has_mul.mul h (mul_monoid_foldr t)  

-- Additive version of the same foldr function.
def add_monoid_foldr 
  {α : Type u} 
  [add_monoid α] 
  :
  list α → α 
| [] := has_zero.zero
| (h::t) := has_add.add h (add_monoid_foldr t)  

#eval mul_monoid_foldr [1,2,3,4,5]
#eval add_monoid_foldr [1,2,3,4,5]   -- missing instance above


def sum_vectrs (l : list vectr) : vectr :=
  add_monoid_foldr l

#eval sum_vectrs [v1,v2,v3,v4]

/-
6. Required for graduate students,
optional extra credit for undergrads.

The set of integers mod p can be viewed
as a field with the usual addition and
multiplication operations mod p. These 
finite fields (with only a finite number 
of elements) play a crucial role in many 
areas of number theory (in mathematics), 
and in cryptography in computer science.


A. [20 points]

Instantiate the field typeclass for
the integers mod 5 (a prime). You 
may and should stub out the proofs 
all along the way using "sorry", but
before you do that, convince yourself
that you are *justified* in doing so.

Use a "fake" representation of the
integers mod 5 for this exercise: as
an enumerated type with five values. 
Call them zero, one, two, three, and
four. Then define two functions, 
z5add and z5mul, to add and multiply
values of this type. You can figure
out the addition and multiplication
tables and just write the functions
by cases to return the right result
in each case. Start with Lean's field
typeclass, see what you need to 
instantiate it, and work backwards, 
recursively applying the same method 
until your reach clases that you can
implement directly. Put your code for
this problem below this comment.

Replace the following "assumptions" 
with your actual definitions (commenting
out the axioms as you replace them). You
can right away right click on "field" and
"go to definition" to see what you need
to do. Solving this problem will require
some digging through Lean library code.
-/
--axioms 
 -- (Z5 : Type) 
 -- (z5add : Z5 → Z5 → Z5)
 -- (z5mul : Z5 → Z5 → Z5)
--  #check field Z5

-- HERE

inductive Z5 : Type
| zero
| one
| two
| three
| four

open Z5

def z5add : Z5 → Z5 → Z5
| one zero := one
| one one := two
| one two := three
| one three := four
| one four := zero
| two zero := two
| two one := three
| two two := four
| two three := zero
| two four := one
| three zero := three
| three one := four
| three two := zero
| three three := one
| three four := two
| four zero := four
| four one := zero
| four two := one
| four three := two
| four four := three
| zero zero := zero
| zero one := one
| zero two := two
| zero three := three
| zero four := four


def z5mul : Z5 → Z5 → Z5
| one zero := zero
| one one := one
| one two := two
| one three := three
| one four := four
| two zero := zero
| two one := two
| two two := four
| two three := one
| two four := three
| three zero := zero
| three one := three
| three two := one
| three three := four
| three four := two
| four zero := zero
| four one := four
| four two := three
| four three := two
| four four := one
| zero zero := zero
| zero one := zero
| zero two := zero
| zero three := zero
| zero four := zero

/-
@[protect_proj, ancestor division_ring comm_ring]
class field (K : Type u) extends comm_ring K, has_inv K, nontrivial K :=
(mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * a⁻¹ = 1)
(inv_zero : (0 : K)⁻¹ = 0)

-/
instance a : comm_ring Z5 := sorry
instance b : has_inv Z5 := sorry
instance c : nontrivial Z5 := ⟨⟨zero, one, by contradiction⟩⟩


instance : field Z5 := ⟨sorry,sorry,sorry,sorry,sorry,sorry,sorry,sorry,sorry,sorry,sorry,sorry,sorry,sorry,sorry,sorry,sorry,sorry,sorry,sorry,sorry,sorry⟩

/-
B. [15 points]

Given that you've now presumably
established that Z5 is a field,
let z5scalr be an abbreviation for
Z5, and z5vectr for Z5 ⨯ Z5. Then
use #eval to evaluate an expression
(that you make up) involving vector 
addition and scalar multiplication
using our new z5vectr objects, i.e., 
vectors over Z5. These vectors will
look like, e.g., (one, three). Work 
out the right answer by hand and
test your code to gain confidence 
that it's working correctly.
-/

-- HERE

abbreviation z5scalr := Z5
--
abbreviation z5vectr := Z5 × Z5
--  and z5vectr for Z5 ⨯ Z5 THIS REQUIRES ANOTHER TYPE CLASS
instance  vv : vector_space Z5 (Z5 × Z5) := sorry

def sc : z5scalr := one
def zv : z5vectr := (one, three)

#eval sc • zv -- EXPECTED ANSWER: (one, three)
#eval zv  + zv -- EXPECTED ANSWER : (two, one)


/-
Take away: Instantiating a typeclass
for a given type can provide a whole
set of operations and notations that
you can use to "do algebra" with that
type. The underlying types themselves
can be very diverse. That is, we can
impose the same abstract interface on
sets of objects of different kinds, 
just as we previously imposed a group
API on the elements of the symmetry 
group, D4, of a square. Here we've now
seen that we can write vector space
algebra computations involving 2-D
vectors over both the rational and
the integers mod 5. It's in this 
sense that instantiating a typeclass
for a type provides a new "API" for
manipulating values of that type.

And while languages such as Haskell
do provide typeclasses, they don't
provide a language in which you can
declaratively express and give proofs
of the "rules" that structures have 
to follow to be valid instances. So,
welcome to Lean, a language in which
you can write mathematics and code,
with strong automated type checking
of both code and proofs. If it has to
be right (which is the case for much
crypto code), maybe write it like so!
-/