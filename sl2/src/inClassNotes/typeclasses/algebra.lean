/-
Using typeclasses to formalize basic algebraic structures,
including notably the "rules" defining such structures. 
-/

namespace alg

universe u

/-
Typeclasses extends hierarchy modeling algebraic hierarchy
-/

@[class]
structure has_zero (α : Type u) :=
(zero : α)


@[class]
structure has_one (α : Type u) :=
(one : α)


/-
A groupoid is a set with a binary operator. The only consraint 
is that the set must be closed under the given binary operator.
Note: there are other definitions of groupoid in mathematics. A
groupoid is also sometimes called a magma. Here, the set is given
by the type, α, and the operator by the field, *mul*.
-/
@[class]  
structure mul_groupoid (α : Type u) :=   
(mul : α → α → α)                    

@[class]  
structure add_groupoid (α : Type u) :=  -- aka mul_groupoid or magma
(add : α → α → α)                       -- mul must be total (closed)

/-
A semigroup is a groupoid in which the operator is *associative*
-/
@[class]
structure mul_semigroup (α : Type u) extends mul_groupoid α :=
(assoc : ∀ (a b c : α), mul a (mul b c) = mul (mul a b) c)

@[class]
structure add_semigroup (α : Type u) extends add_groupoid α :=
(assoc : ∀ (a b c_1 : α), add a (add b c_1) = add (add a b) c_1)

/-
A monoid is a semigroup with an identity element
-/
@[class]
structure mul_monoid (α : Type u) extends mul_semigroup α, has_one α :=
(ident_left : ∀ (a : α), mul one a = a)
(ident_right: ∀ (a: α), mul a one = a)

@[class]
structure add_monoid (α : Type u) extends add_semigroup α, has_zero α :=
(ident_left : ∀ (a : α), add zero a = a)
(ident_right: ∀ (a: α), add a zero = a)

/-
A group is a mul_monoid in which every element has an inverse
-/
@[class]
structure mul_group (α : Type u) extends mul_monoid α :=
(left_inv : ∀ (a : α), ∃ (i : α), mul i a = one )
(right_inv : ∀ (a : α), ∃ (i : α), mul a i = one )

@[class]
structure add_group (α : Type u) extends add_monoid α :=
(left_ident : ∀ (a : α), ∃ (i : α), add i a = zero )
(right_ident : ∀ (a : α), ∃ (i : α), add a i = zero )

/-
A group is commutative, or abelian, if its operator is commutative.
-/
@[class]
structure mul_comm_group (α : Type u) extends mul_group α :=
(comm : ∀ (a b : α), mul a b = mul b a )

@[class]
structure add_comm_group (α : Type u) extends add_group α :=
(comm : ∀ (a b : α), add a b = add b a )

set_option old_structure_cmd true

class has_ring (α : Type u) 
  extends alg.add_comm_group α, mul_monoid α :=
(dist_left : ∀ (a b c : α), 
  mul_groupoid.mul a (add_groupoid.add b c) = 
  add_groupoid.add (mul_groupoid.mul a b) (mul_groupoid.mul a c))
(dist_right : ∀ (a b c : α), 
  mul_groupoid.mul (add_groupoid.add b c) a = 
  add_groupoid.add (mul_groupoid.mul b a) (mul_groupoid.mul c a))

class has_module (α β : Type) extends has_ring α, add_group β :=
(add_comm : ∀ (b1 b2 : β), add_groupoid.add b1 b2 = add_groupoid.add b2 b1)
(scale : α → β → β)
(rule1: ∀ (a1 a2 : α) (b : β), scale (mul_groupoid.mul a1 a2) b = scale a1 (scale a2 b) )
(rule2: ∀ (a : α) (b1 b2 : β), scale a (add_groupoid.add b1 b2) = add_groupoid.add (scale a b1) (scale a b2))



-- class vector_space 

/-
You can keep going to define a whole hierarchy of algebraic
abstractions, and indeed all of these constructs and many more
are already defined in Leans math library.

-- Ring
-- Field
-- Module
-- Vector space
-- etc.
-/


/-
Typeclass instances for nat. Note that we are "stubbing out"
proofs that our objects actually follow the rules. We will 
come back to fill in proofs once we know how to do that. It
will be soon.
-/
instance has_one_nat : has_one nat := ⟨ 1 ⟩ 
instance mul_groupoid_nat : mul_groupoid nat := ⟨ nat.mul ⟩ 
instance mul_semigroup_nat : mul_semigroup nat := ⟨ _ ⟩ 
instance mul_monoid_nat : mul_monoid nat := ⟨ _ , _ ⟩ 

instance has_zero_nat : has_zero nat := ⟨ 0 ⟩ 
instance add_groupoid_nat : add_groupoid nat := ⟨ nat.add ⟩ 
instance add_semigroup_nat : add_semigroup nat := ⟨ _ ⟩ 
instance add_monoid_nat : add_monoid nat := ⟨ _ , _ ⟩ 

-- instance mul_group_nat : mul_group nat := ⟨ _, _ ⟩ 

/-
ℕ isn't a group under either add or mul! No inverses. 
ℤ is an additive group but not a multiplicative group.
ℚ is an additive group; ℚ-{0} is a multiplicative group.
ℚ is thus a field. ℝ is a field in the same way. So is ℂ.
-/ 



/-
So what good can all of this be? Here's one application.
We've noted that arguments to foldr can be inconsistent. The
wrong identity element can be passed for the given operator.
-/


def foldr {α : Type} : (α → α → α) → α → list α → α 
| f id [] := id    
| f id (h::t) := f h (foldr f id t)

#eval foldr nat.mul 0 [1,2,3,4,5]   -- oops!


/-
A better foldr takes a "certified" monoid as an argument.
A monoid bundles an operator with its identity element, so
they can't get out of synch. By "certified,"" we mean that 
an object comes with a rock solid proof of correctness. In
this case, we'd really want to fill a proof that a putative
monoid instance has an identity element that is proven to
be a left and a right identity for the given operator. We
don't know quite yet how to give these proofs, but that's
the idea.  

Here are implementations of foldr taking multiplicative and
additive monoids as arguments. Note that the code is written
to depend only on the definitions of the relevant typeclasses.
You can thus use this fold to reduce lists of values of any 
type as long as that type provides an implementation of the 
monoid typeclass.  

NB: typeclass instances should almost always be anonymous. 
For exaple, write [mul_monoid α] instead of [m : mul_monoid α]. 
Lean does NOT support dot notation for typeclass instances.
Look carefully below: Lean infers an instance of mul_monoid.
That instance in turn extends has_one and mul_semigroup. The
latter extends mul_groupoid (formerly, and in Lean, has_mul).
To get at the mul function of the monoid that we need here,
we refer to it through the typeclass, up the inheritance
hierarchy, that defines it directly: here, mul_groupoid.
-/
def mul_monoid_foldr 
  {α : Type u} 
  [mul_monoid α] 
  :
  list α → α 
| [] := has_one.one
| (h::t) := mul_groupoid.mul h (mul_monoid_foldr t)  

-- Additive version of the same foldr function.
def add_monoid_foldr 
  {α : Type u} 
  [add_monoid α] 
  :
  list α → α 
| [] := has_zero.zero
| (h::t) := add_groupoid.add h (add_monoid_foldr t)  

#eval mul_monoid_foldr [1,2,3,4,5]
#eval add_monoid_foldr [1,2,3,4,5]   -- missing instance above


/-
The group, D4.
-/

inductive dihedral_4 : Type
| r0     -- 0 quarter turns    r: rotation
| r1     -- 1 quarter turn
| r2     -- 2 quarter turns
| r3     -- 3 quarter turns
| sr0    -- flip horizontal   s: reflection
| sr1    -- flip ne/sw
| sr2    -- flip vertical
| sr3    -- flip nw/se

open dihedral_4

def e := r0

def d4_mul : 
  dihedral_4 → dihedral_4 → dihedral_4  -- closed
:= 
_

/-
r^n is still a rotation
sr^n and r^ns are reflections
-/

instance d4_has_one : has_one dihedral_4 := ⟨ e ⟩ 
instance d4_has_groupoid : mul_groupoid dihedral_4 := ⟨ d4_mul ⟩
instance d4_has_semigroup : mul_semigroup dihedral_4 := ⟨ sorry ⟩
instance d4_has_monoid : mul_monoid dihedral_4 := ⟨ sorry, sorry ⟩ 

#reduce mul_monoid_foldr [r3, r1, sr3, r2]

end alg

