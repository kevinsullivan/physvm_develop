import .affnK
import linear_algebra.std_basis
import .affnKcoord_definitions

/-
    ********************
    *** Vector space ***
    ********************
-/
universes u

section implicitK

variables 
{K : Type u} [field K] [inhabited K] 
{dim : nat} {id_vec : fin dim → nat }{f : fm K dim id_vec} (s : spc K f)
{dim2 : nat } {id_vec2 : fin dim2 → nat} {f2 : fm K dim2 id_vec2} (s2 : spc K f2)


variables v1 v2 : vectr s
/-
Standard vector space operations
-/
@[simp]
def add_vectr_vectr (v1 v2 : vectr s) : vectr s :=  mk_vectr' s (v1.coords + v2.coords)
@[simp]
def smul_vectr (k : K) (v : vectr s) : vectr s := mk_vectr' s (k • v.coords)
@[simp]
def neg_vectr (v : vectr s) : vectr s := mk_vectr' s ((-1 : K) • v.coords)
@[simp]
def sub_vectr_vectr (v1 v2 : vectr s) : vectr s := add_vectr_vectr s v1 (neg_vectr s v2)

-- See unframed file for template for proving module
/-
Begin proofs below. Set of lemmas and type class instances culminating in a 
proof that vectr s and point s form an affine space.
-/
instance has_add_vectr : has_add (vectr s) := ⟨add_vectr_vectr s⟩
--addition of vectrs is associative
lemma add_assoc_vectr : ∀ a b c : vectr s, a + b + c = a + (b + c) := 
begin
    intros,
    ext,
    have p1 : (a + b + c).coords = a.coords + b.coords + c.coords := rfl,
    have p2 : (a + (b + c)).coords = a.coords + (b.coords + c.coords) := rfl,
    rw [p1,p2],
    dsimp only [has_add.add],
    dsimp only [add_vec_vec],
    simp only [add_assoc]
end

--vectrs form an additive semigroup
instance add_semigroup_vectr : add_semigroup (vectr s) := ⟨ add_vectr_vectr s, add_assoc_vectr s⟩ 

#check list.eq_repeat

--definition of zero vectr
@[simp]
def vectr_zero := mk_vectr s ⟨list.repeat 0 dim, begin
        simp  *
    end⟩--@mk_vectr K _ _ n f s (0:K)
instance has_zero_vectr : has_zero (vectr s) := ⟨vectr_zero s⟩

--zero vectr plus any particular vectr is the particular vectr unchanged 
lemma zero_add_vectr : ∀ a : vectr s, 0 + a = a := 
begin
    intros, ext,
    dsimp only [has_add.add],
    dsimp only [add_vectr_vectr],
    simp only [mk_vectr'],
    dsimp only [has_add.add],
    dsimp only [add_vec_vec],
    dsimp only [has_zero.zero],
    dsimp only [vectr_zero],
    simp only [mk_vectr, mk_vec_n, vector.nth, mk_vec, list.nth_le_repeat, zero_add],
end

/-
any vectr plus the 0 vectr is the original vectr
-/
lemma add_zero_vectr : ∀ a : vectr s, a + 0 = a := 
begin
    intros, ext,
    dsimp only [has_add.add],
    dsimp only [add_vectr_vectr],
    simp only [mk_vectr'],
    dsimp only [has_add.add],
    dsimp only [add_vec_vec],
    dsimp only [has_zero.zero],
    dsimp only [vectr_zero],
    simp only [mk_vectr, mk_vec_n, vector.nth, mk_vec, list.nth_le_repeat, add_zero],
end

/-
helper function for updated lean type classes
-/
@[simp]
def nsmul_vectr : ℕ → (vectr s) → (vectr s) 
| nat.zero v := vectr_zero s
--| 1 v := v
| (nat.succ n) v := (add_vectr_vectr _) v (nsmul_vectr n v)

/-
vectrs form an additive monoid
-/
instance add_monoid_vectr : add_monoid (vectr s) := ⟨ 
    -- add_semigroup
    add_vectr_vectr s, 
    add_assoc_vectr s, 
    -- has_zero
    vectr_zero s,
    -- new structure 
    zero_add_vectr s, 
    add_zero_vectr s,
    nsmul_vectr s
⟩

/-
negation and subtraction instances
-/
instance has_neg_vectr : has_neg (vectr s) := ⟨ neg_vectr s ⟩
instance has_sub_vectr : has_sub (vectr s) := ⟨ sub_vectr_vectr s ⟩ 

/-
subtracting a vectr is equivalent to adding the inverse
-/
lemma sub_eq_add_neg_vectr : ∀ a b : vectr s, a - b = a + -b := 
begin
    intros,ext,
    refl
end 

/-
@[protect_proj, ancestor add_monoid has_neg has_sub]
class sub_neg_monoid (G : Type u) extends add_monoid G, has_neg G, has_sub G :=
(sub := λ a b, a + -b)
(sub_eq_add_neg : ∀ a b : G, a - b = a + -b . try_refl_tac)
(gsmul : ℤ → G → G := gsmul_rec)
(gsmul_zero' : ∀ (a : G), gsmul 0 a = 0 . try_refl_tac)
(gsmul_succ' :
  ∀ (n : ℕ) (a : G), gsmul (int.of_nat n.succ) a = a + gsmul (int.of_nat n) a  . try_refl_tac)
(gsmul_neg' :
  ∀ (n : ℕ) (a : G), gsmul (-[1+ n]) a = - (gsmul n.succ a) . try_refl_tac)

-/
instance sub_neg_monoid_vectr : sub_neg_monoid (vectr s) :=
{
    neg := neg_vectr s,
    ..(show add_monoid (vectr s), by apply_instance)
}

/-
adding a vectr with its inverse yields the 0 vectr
-/
lemma add_left_neg_vectr : ∀ a : vectr s, -a + a = 0 := 
begin
    intros,
    ext,
    dsimp only [has_add.add],
    dsimp only [add_vectr_vectr],
    simp only [mk_vectr'],
    dsimp only [has_add.add],
    dsimp only [add_vec_vec],
    dsimp only [has_zero.zero],
    dsimp only [vectr_zero],
    simp only [mk_vectr, mk_vec_n, vector.nth, mk_vec, list.nth_le_repeat],
    dsimp only [has_neg.neg],
    dsimp only [neg_vectr],
    dsimp only [has_scalar.smul],
    simp only [neg_mul_eq_neg_mul_symm, one_mul, mk_vectr', add_left_neg, smul_vec],
end

/-
vectrs form an additive group
-/
instance : add_group (vectr s) := {
    add_left_neg := begin
        exact add_left_neg_vectr s,
    end,
..(show sub_neg_monoid (vectr s), by apply_instance),

}

/-
vectr addition is commutative
-/
lemma add_comm_vectr : ∀ a b : vectr s, a + b = b + a := 
begin
    intros,
    ext,
    repeat {
    have p1 : (a + b).coords = a.coords + b.coords:= rfl,
    have p2 : (b + a).coords = b.coords + a.coords := rfl,
    rw [p1,p2],
    cc
    } ,
    dsimp only [has_add.add],
    dsimp only [add_vectr_vectr],
    dsimp only [mk_vectr'],
    dsimp only [has_add.add],
    dsimp only [add_vec_vec],
    simp only [add_comm]
end

/-
vectrs form an additive commutative semigroup
-/
instance add_comm_semigroup_vectr : add_comm_semigroup (vectr s) := ⟨
    -- add_semigroup
    add_vectr_vectr s, 
    add_assoc_vectr s,
    add_comm_vectr s,
⟩

/-
vectrs form an additive commutative monoid
-/
instance add_comm_monoid_vectr : add_comm_monoid (vectr s) := 
{
    add_comm := begin
        exact add_comm_vectr s
    end, 
    ..(show add_monoid (vectr s), by apply_instance)
}



instance has_scalar_vectr : has_scalar K (vectr s) := ⟨
smul_vectr s,
⟩

/-
the unit scalar times a vectr is the same vectr
-/
lemma one_smul_vectr : ∀ b : vectr s, (1 : K) • b = b := begin
    intros,ext,
    repeat {
        have h0 : ((1:K) • b).coords = ((1:K)•(b.coords)) := rfl,
        rw [h0],
        simp *,
    }
end

/-
scalars multiplication associative with vectr multiplication
-/
lemma mul_smul_vectr : ∀ (x y : K) (b : vectr s), (x * y) • b = x • y • b :=
begin
    intros,
    cases b,
    ext,
    exact mul_assoc x y _,
end

/-
@[protect_proj, to_additive]
class mul_action (α : Type*) (β : Type*) [monoid α] extends has_scalar α β :=
(one_smul : ∀ b : β, (1 : α) • b = b)
(mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b)
-/
instance mul_action_vectr : mul_action K (vectr s) := ⟨
one_smul_vectr s,
mul_smul_vectr s,
⟩ 

/-
scalars are distributive over vectrs
-/
lemma smul_add_vectr : ∀(r : K) (x y : vectr s), r • (x + y) = r • x + r • y := begin
    intros, ext,
    repeat {
    have h0 : (r • (x + y)).coords = (r • (x.coords + y.coords)) := rfl,
    have h1 : (r•x + r•y).coords = (r•x.coords + r•y.coords) := rfl,
    rw [h0,h1],
    simp *,
    }

end

/-
any scalar times the 0 vectr is the 0 vectr
-/
lemma smul_zero_vectr : ∀(r : K), r • (0 : vectr s) = 0 := begin
    intros,
    ext,
    dsimp only [has_scalar.smul],
    dsimp only [smul_vectr],
    dsimp only [has_scalar.smul],
    dsimp only [mk_vectr'],
    dsimp only [smul_vec],
    dsimp only [has_zero.zero],
    simp only [vectr_zero, mk_vectr, mk_vec_n, mk_vec, vector.nth, list.nth_le_repeat, mul_zero],
end

/-
class distrib_mul_action (M : Type*) (A : Type*) [monoid M] [add_monoid A]
  extends mul_action M A :=
(smul_add : ∀(r : M) (x y : A), r • (x + y) = r • x + r • y)
(smul_zero : ∀(r : M), r • (0 : A) = 0)
-/
instance distrib_mul_action_K_vectrK : distrib_mul_action K (vectr s) := ⟨
smul_add_vectr s,
smul_zero_vectr s,
⟩ 

-- vectrs are distributive over scalars
lemma add_smul_vectr : ∀ (a b : K) (x : vectr s), (a + b) • x = a • x + b • x := 
begin
  intros,
  ext,
  exact right_distrib _ _ _,
end

--0 scalar times any vectr is 0 vectr
lemma zero_smul_vectr : ∀ (x : vectr s), (0 : K) • x = 0 := begin
    intros,
    ext,
    dsimp only [has_scalar.smul],
    dsimp only [smul_vectr],
    dsimp only [has_scalar.smul],
    dsimp only [mk_vectr'],
    dsimp only [smul_vec],
    have h₁ : ((0 : vectr s).coords x_1).coord = 0 := begin
        dsimp only [has_zero.zero],
        simp only [vectr_zero, mk_vectr, mk_vec_n, mk_vec, vector.nth, list.nth_le_repeat, mul_zero],
        refl
    end,
    rw h₁,
    simp only [zero_mul]
end

--vectors form an additive commutative group
instance add_comm_group_vectr : add_comm_group (vectr s) := 
{
    add_comm := begin
        exact add_comm_vectr s
        
    end,
..(show add_group (vectr s), by apply_instance)
}

--Result of file is a proof that K and vectr s are a vector space (module technicaly, but vector space effectively)

instance module_K_vectrK : module K (vectr s) := ⟨ 
    add_smul_vectr s, 
    zero_smul_vectr s, 
⟩ 

end implicitK
