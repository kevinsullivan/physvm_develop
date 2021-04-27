





/-
Terminology: INTRODUCTION RULES
-/

/-
The constructors of a type implement
what in logic and computation we can
call *introduction* rules. They give
us ways to *introduce* vaues of some
particular type.
-/



/-
Inference rule notation.
-/

/-
There are two introduction rules for bool

  Γ ⊢ bool.tt : bool   -- bool_intro_tt
  Γ ⊢ bool.ff : bool   -- bool_intro_ff

The capital Greek letter Gamma (Γ) stands
for an set of definitions assumed already
to be given. The turnstile character (⊢)
means that "in this context it is possible
to deduce the "type judgement" after the
turnstile. Concretely, here, the rules say
that "in any context, without any further
assumptions, we can deduce that bool.tt is
a value of type bool (and the same goes
for bool.ff).

In logical terms, you can read such a rule
as *asserting* that if the definitions in 
the context are assumed to be true (we can
think of these as premises or preconditions)
then it's possible to derive the truth of
the "judgment" that comes below the line 
(after the turnstile).


The preceding notation above is "inline" 
notation (context ⊢ judgment) and is used
for giving short inference rules. Dispay 
notation, illustrated below, is generally
used intead when rules are too long to be
readable on one line. Here the context is 
above the line; the line is used instead 
of the turnstile; a judgment is given below 
the line; and the name of the inference
rule is given to the right of the line. 
We will often attach _intro or _I to the 
name of a rule to indicate that it's an
introduction rule. 

  Γ
------ bool_intro.tt
 bool

   Γ
------ bool_intro.ff
 bool

Note also that if there really are no
preconditions on the context for the
application of a rule, the Γ is often
left out.

 
------ bool_intro.tt
 bool


------ bool_intro.ff
 bool


In logic, an introduction rule with
no preconditions is called an axiom.
It allows us to make certain judgments
without already knowing anything else
at all.

The constructors of inductive types
can be read as type-speific axioms.
The constructor "| tt : bool", for
example, says that are given the type
judgment, tt : bool, "for free". We
can assume it's true with the need
for any prior or additional evidence.

EXERCISE: How many introduction rules
are there for the day type?

Here are introduction rules for some
of our other types

While constructors can be read as axioms,
which is to say that we can always assume
they're valid, sometimes to apply or use
such a rule, we do need certain additional
assumptions to be true.

Consider the box constructor, mk. A way
to read it is that "If we may assume that
n is a value of type ℕ then we may infer
that the term (box_ℕ.mk n) is of type 
box_ℕ."

Γ, (n : ℕ) ⊢ (box_ℕ.mk n) : box_ℕ 

     Γ, (n : ℕ)
---------------------- box_ℕ_intro
 (box_ℕ.mk n) : box_ℕ 

 Note that such rules often leave out
 the full statement of the type judgment
 below the line (after the turnstile).Type

      Γ, (n : ℕ)
---------------------- box_ℕ_intro
        box_ℕ 

This just says that in a context in which
I have that n is of type nat, I can use the
box_ℕ_intro rule to construct a value of 
type box_ℕ.

 NB! There's really nothing new here
 at all. All we're really doing here 
 it representing the *types* of available
 constructors (introduction rules) using 
 a sort of textual notation (inline or
 display). Here's one of the ways we 
 wrote the same information above.

| mk (n : ℕ) : box_ℕ 

Constructors are introduction rules 
that we take as axioms, i.e., as being
given, defined, and available for use.
That said, these axioms are often in
the form of implications that do require
some additional conditions to be true
before they can be used to derive given
conclusions. For example, the box_ℕ 
introduction rule does require that we
can assume that (n : ℕ). You can think
of *arguments* to constructors (and to
functions more generally) as assumptions
that have to be satisfied before the
constructor or function can be used!
 
Constructors are introductions rules
that are accepted as axioms

Arguments to constructors are additional
assumptions that have to be true before 
such rules can be applied to derive the
given conclusions.

In general, inference rules can require
that multiple assumptions be true before
a conclusion can be drawn.

Γ, (n : ℕ) (s : string)
----------------------- prod_ℕ_string_intro
(mk n s) : prod_ℕ_string

Give a context containing at least the
assumptions that (n : ℕ) and (s : string)
this inference rules allows us to deduce
that we can construct and object (mk n s)
of type prod_ℕ_string. 

Constructors are "introduction" inference 
rules that end with the construction of a
a new object with the specified type.
-/

/-
There's really nothing mysterious about
this notation. It's basically a way of
explaining/claiming that in a specified
context, i.e., contingent on a given set
of assumptions, some object of a certain
type can be constructed. 
-/


/-
Terminology: ELIMINATION RULES

Where introduction rules explain how we can
form new terms (objects, values) of specific
types, ELIMINAATION rules tell us how we can
USE objects of given type (to form objects of
other types). 

To use an object of some type, we often need to
DESTRUCTURE it: to take it apart to see both
the constructor that was used to form it and
the arguments (if any) that were supplied to
the constructor when the object was created.

Consider the following elimination rule. 

         Γ, (d : day)
---------------------------- day_elim
(e, p) : Σ (d : day), e ≠ d

We assume we're in a context in which we're
given a day d, and we then "use" d to pick
a different day, e, which we return as the
first element of a pair, along with evidence
that e really is a different day.

Can we prove to ourselves that this rule is
actually realizable? It seems like it should
be possible. For example, given a day, d, we
can always pick "the next" day as e, and then
we just need a little "proof" that e really 
is not the same day as d.

Now here's a crucial point. To use a value 
of a sum type, here of type day, we will often 
have to perform a case analysis, to determine 
which of several possible "forms" of value 
we're looking at (which constructor was used
to introduce the value in the first place).
-/

def next_day : day → day
| sun := mon
| mon := tue
| tue := wed
| wed := thu
| thu := fri
| fri := sat
| sat := sun

#reduce next_day tue

def exists_different_day (d : day) : ∃ (e : day), e ≠ d :=
  exists.intro 
    (next_day d) 
    (by begin 
      cases d,          -- consider each possible day, d
      simp [next_day],  -- apply rules in next_day + "magic"
      simp [next_day],  -- do the same thing for each case
      simp [next_day],
      simp [next_day],
      simp [next_day],
      simp [next_day],
      simp [next_day],
  end) 

#reduce (exists_different_day sat)    -- Yikes :-)


/-
Lots of things to say, here:

1. Inference rule notation

      Γ, (d : day)
----------------------- day_elim_different_day
pf : ∃ (e : day), e ≠ d

2. Lean is language in which we can compute with
logical propositions and proofs just as easily as
we can compute with natural numbers, bools, strings,
and so forth. This puts it in a completely different
class of languages than mere functional languages, 
such as Haskell, OCaml, Scheme, etc.

3. We see in this example that in the logical framework
that Lean presents, propositions are represented as 
types, and proofs of propositions are simply values of 
such types. Moreover, the type checker ensures that 
proofs are of the right types -- that the prove the
propositions they are claimed to prove. If P is a type
that represents a proposition, and we have (pf : P), 
just as if (n : ℕ) type checks, we can be *sure* that
n really is a term of type ℕ!

4. Clearly it's going to be super-important to learn 
about types. In fact, Lean is really just implements
one particular version of the theoretical field of CS
called type theory.

5. Type theory is so expressive that it provides us
with what we call a logical framework, which is a 
language within which we can define and automate many
other logics, and many other languages, more broadly,
including such languages as C, Python, etc. We have
already implemented the syntax and semantics of one
very simple language of (a few) Roman numberals.

6. Note that we picked a particular implementation,
next day, to pick a "witness" to the proposition that
there's a different day for each possible argument of
type day. The witness selected when d := wed, for 
example, is thu. We could have used a different 
witness-picking function, such as one that returns
the previous day, as long as it really does *always*
return a day that's different than the one given as 
an argument. 

7. If our witness-picking function has a bug, then 
our proof-constructing function will fail, because
there will be some day for which the chooser will 
choose them same day as a "e", the intended witness,
and it will then be impossible to construct the proof
that e ≠ d. The lean proof checker can can find bugs
in programs relative to a logical *specifications* of 
their required behaviors.

Exercise: make a small change to next_day so that 
it no longer *always* returns a day different from
the one given, and then find exactly where the type
checker raises an error.

Phew, that was a lot! Some of you don't even have a 
firm grasp of what we mean by a proposition or a proof.
No worries, this was just a little "exposure." Are you
feeling sunburned?

To bring it back to where we started, elimination rules
are simply "rules" (often just funtions) for *consuming* 
rather than *constructing* values of a given type. 

Ehen the type of object being consumed is a sum type,
we generally need to do a case analysis to determine
which variant we've been given as a value. 

The next_day function is a good example: it consumes
a *day* value, does a case analysis to figure out which 
constructor/variant is assumed to have been given as an
argument, then computes and returns a result accordingly.  

As a second example of a day-elimination (day-consuming)
function/rule, we defined different_day as a function
that uses/consumes a value of type day and returns (if
you prefer, introduces) a value that proves that there 
is *some* day different than the one consumed.
-/

-- ELIMINATION/USE OF VALUES OF PRODUCT TYPES

/-
Inference rule notation

 Γ, (n : ℕ) (s : string)
------------------------ prod_intro
 ⟨n, s⟩ : Prod_ℕ_string


Γ, ⟨n, s⟩ : prod_ℕ_string
------------------------- prod_elim_fst
        n : ℕ 


Γ, ⟨n, s⟩ : prod_ℕ_string
------------------------- prod_elim_snd
        s : string
-/


end hidden