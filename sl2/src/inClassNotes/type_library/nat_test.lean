import .nat

namespace hidden

/-
Finally, nat: a properly inductive
type, where larger values of this
type are constructed using smaller
values *of the same type*.
-/

def n0  := nat.zero
def n1  := 
  nat.succ
    _ 

def n2  := 
  nat.succ  
    _

variable n : nat    -- assume (n : nat)
#check nat.succ n   -- succ is also nat


/-
To fully understand how this
definition produces a set of 
terms that we can view interpret
as representing natural numbers, 
you need a few additional facts:

(1) Constructors are *disjoint*. This 
means that terms built using different
constructors are never equal. So zero
is not equal to any successor of zero.

(2) Constructors are *injective*. This
means applying a constructor different
argument values always yields different
results. It's especially useful in many
cases to think of this rule backwards:

(n : ℕ) (m : ℕ) (h: succ n = succ m) 
-------------------------------------
            (n = m)

Injective means that different values
are sent to different places. So if 
succ is injective and it sends both 
n and m to the same value, then n and
m must have the same value. So now, for
example, we can't have succ 5 = zero 
(which would be the case for ℕ mod 5.)

(3) The values of a type include *all*
values obtainable by any *finite* number
of applications of its constructors. In
other words, a type is "closed" under
finite applications of its constructors.
So (succ n) is a nat for *any* n.

(4) A type defines the *smallest* set 
of values closed under applications of
its constructors. There are not values
in a type that "creep in" wihtout being
constructed by some finite number of
applications of available constructors.

What this means is that if we're given
*any* value of a type, it *must* have 
been constructed using some constructor.
applied to some arguments, and we can
recover those specific arguments. This 
fact allows us to know that when we do 
case analysis by constructor, we are
sure to match *any* value of any type.
-/

/-
The key to writing functions that take nat
arguments is, as usual, case analysis. If
we're given a natural number (term of type
ℕ), n, we first determine which constructor
was used to create it (zero or succ), and if
it was succ, then what one-smaller nat value
succ was applied to to produce our argument.
-/

/-
Zero. Zero is the smallest natural number.
It is implemented by the zero constructor.
-/

#eval nat.zero

/-
Successor. The successor function takes a
nat and yields a one-bigger nat. It is
implemented by the succ constructor. This
constructor takes a term of type nat as 
an argument and constructs/returns a new
term with one additional "succ" at its
front.
-/

#eval nat.succ nat.zero
#eval nat.succ 
        _
#eval nat.succ 
        (nat.succ
          (nat.succ
            _
          )
        )

/-
Inductive data type definitions define
this kind of "tree-structured" data. In
this case each "node" is either "zero" or
"succ" and another "node"

zero

succ
 |
zero

succ 
 |
succ
 |
... any finite number of times
 |
zero
-/
          

/-
We've now see how nat is defined.
We close the hidden name space and
just use Lean's nats from now on.
The benefit is that we get additional
Lean notations.
-/


-- Compare this with what follows.
#reduce nat.succ (nat.succ nat.zero)

end hidden

/-
NOTATION (concrete syntax)
-/

#eval nat.succ (nat.succ nat.zero) -- yay

#check 2

variable (n : nat)

/-
The notation 2 *could* have been defined
to mean (2 : nat), (2 : ℚ), (2 : ℝ), or
(2 : ℂ), or even something else, but in Lean
it's *hardwired* to mean (2 : ℕ) by default.
If you want a 2 of type rational, real, or
complex, for example, you have to say so
explicitly, and you have to have imported
the necessary math library. We skip that
for now.
-/


/-
FUNCTIONS
-/


def is0 : ℕ → bool
| nat.zero := tt
| _ := ff 

def inc (n : ℕ) := nat.succ n

def pred' : nat → nat
| nat.zero := nat.zero
| (nat.succ n') := n' 

#eval pred' 0
#eval pred' 1
#eval pred' 5

-- equivalent
def pred : nat → nat
| nat.zero := nat.zero
| (n' + 1) := n' 

-- this notation won't work
def pred'' : nat → nat
| nat.zero := nat.zero
| 1 + n := n' 

-- subtle difference in notations here
#reduce n + 1   -- succ n
#reduce 1 + n   -- nat.add 1 n
#reduce n + 2 
#reduce 2 + n
-- can only match constructor expressions

/-
Because larger values of type nat are
constructed from smaller values of the
same type, many functions that consume
a nat argument will work by applying
themselves recursively to smaller values
of the same type.
-/

def double : ℕ → ℕ 
| nat.zero := 0   -- 0 is nat.zero     
| (nat.succ n') := double n' + 2

def div2 : ℕ → ℕ 
| 0 := 0
| 1 := 0
| (n' + 2) := div2 n' + 1 

#eval div2 5

-- Exercise: define mod2

def fac : ℕ → ℕ 
| 0 := 1
| (n' + 1) := (n' + 1) * fac n'

def fib : ℕ → ℕ 
| 0 := 1
| 1 := 1
| (n' + 2) := fib (n' + 1) + fib n'

#eval fib 5

/- 
Exercise: On a piece of paper, draw
the computation tree for fib 5.

                  fib 5
                /      \
              fib 4   fib 3
            /     \    /\ ...
          fib 3   fib 2
        /     \    /\ ...
      fib 2  fib 1
     /     \  /\ ...
   fib 1  fib 0
    |       |
    1       1
-/

/-
Addition:
0         + m = m
(n' + 1)  + m = (n' + m) + 1
Be sure you understand that!
-/

def add : ℕ → ℕ → ℕ 
| 0        m :=   m 
| (n' + 1) m := (add n' m) + 1


/-
EXERCISE: write a mathematical
definition of multiplication of
n by m, then implement it, using
your add function if/as necessary
to carry out addition.
-/

/-
EXERCISE: write a mathematical
definition of exponentiation and
implement it, using your definition
of multiplication if/as necessary.
-/

/-
Addition is iterated increment.
Multiplication is iterated addition.
Exponentiation is iterated multiplication. 
What function is iterated exponentiation?
Exercise: implement it.
-/