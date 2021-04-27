# Ad Hoc Polymorphism; Overloading; Typeclasses

## Introduction

Our next topic is that of ad hoc polymorphism,
leading into generalized algebraic structures.

Let's start by discussing arithmetic addition
in a language such as C or Java. The salient
point here is that we can write expressions,
such as the following, both of which use the +
operator, but that have different types.

- 1   + 1
- 1.0 + 1.0

The first plus really means "the plus function
defined for int values, while the second means
the plus function defined for floating points."

Yes, there really are two completely different
functions behind those two instances of the +
operator.

## Ad Hoc Polymorphism; Operator Overloading

This example illustrates what we call ad hoc
polymorphism, and specifically in this case what
we call "operator overloading". The term means
that the same operator name or symbol (here +)
is bound to different meanings depending on 
*the types* of the argument(s) to which it is
applied. 

The determination of which function value to
bind it to is made statically (e.g., by a C++
compiler, as well as in Lean).

Overloading in this sense involves associating
a value (here a function value) with each of one
or more types (here int and floating point). In
our example, a floating_point_add function is
associated with the float type and integer_add
is associated with the int type. 

Now when the compiler (or the "elaborator" in 
Lean) sees an application of the overloaded
operator, +, to  arguments, it determines the 
types of the arguments, then *looks up the 
associated function value and uses it in place 
of the overloaded operator.*

## Next Steps

So how do these associations, between types on
hand and values on the other, how do they get
set up, and once set up, how can we use them?