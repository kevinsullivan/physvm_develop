import .aff1K
import linear_algebra.affine_space.affine_equiv

/-
Framed points, vectors, frames
-/

universes u 

section explicitK

variables 
(K : Type u) [field K] [inhabited K] 

/-
Is this where we root distinctions between affine spaces for different dimensionss?
-/
inductive fm : nat → Type u
| base : Π n, fm n
| deriv : Π n, (prod (pt K) (vec K)) → fm n → fm n  -- TODO: curry all of these args

/-
inductive fm : nat → Type u
| base : ∀ (n : nat), fm n
| deriv : ∀ (n : nat), (prod (pt K) (vec K)) → fm n → fm n
-/

def mk_fm  {n : nat } (p : pt K) (v : vec K) (f : fm K n): fm K n := fm.deriv n (p, v) f 

structure spc {n : nat} (f : fm K n) : Type u       -- interesting specimen, here, btw

def mk_space {n : nat} (f : fm K n) :=
  @spc.mk K _ _ n f 

end explicitK

section implicitK

variables 
{K : Type u} [field K] [inhabited K] 
{n : nat} {f : fm K n} (s : spc K f)

/-
Augment pt and vec types with spaces and frames and
then make operations apply only for objects in same
space (and thus frame).
-/
@[ext]
structure point {f : fm K n} (s : @spc K _ _ n f ) extends pt K
@[simp]
def mk_point' (p : pt K) : point s := point.mk p  
@[simp]
def mk_point (k : K) : point s := point.mk (mk_pt K k)  

def p := mk_point s (3:K)

@[ext]
structure vectr {f : fm K n} (s : spc K f ) extends vec K
@[simp]
def mk_vectr' (v : vec K) : vectr s := vectr.mk v
@[simp]
def mk_vectr (k : K) : vectr s := vectr.mk (mk_vec K k)  

-- note that we don't extend fm
def mk_frame {parent : fm K n} {s : spc K parent}  (p : point s) (v : vectr s) :=
fm.deriv n (p.to_pt, v.to_vec) parent   -- TODO: make sure v ≠ 0 (erasing tyoe info)
                                      -- TODO: snd arg is really a basis for the vs


/-
    *************************************
    Instantiate vector_space K (vector K)
    *************************************
-/

variables v1 v2 : @vectr K _ _ n f s
#check v1.to_vec
#check v2.to_vec + v1.to_vec

@[simp]
def add_vectr_vectr (v1 v2 : vectr s) : vectr s :=  mk_vectr' s (v1.to_vec + v2.to_vec)
@[simp]
def smul_vectr (k : K) (v : vectr s) : vectr s := mk_vectr' s (k • v.to_vec)
@[simp]
def neg_vectr (v : vectr s) : vectr s := mk_vectr' s ((-1 : K) • v.to_vec)
@[simp]
def sub_vectr_vectr (v1 v2 : vectr s) : vectr s := add_vectr_vectr s v1 (neg_vectr s v2)

-- See unframed file for template for proving vector_space

instance has_add_vectr : has_add (vectr s) := ⟨add_vectr_vectr s⟩
lemma add_assoc_vectr : ∀ a b c : vectr s, a + b + c = a + (b + c) := 
begin
    intros,
    ext,
    --cases a,
    repeat {
    have p1 : (a + b + c).to_vec = a.to_vec + b.to_vec + c.to_vec := rfl,
    have p2 : (a + (b + c)).to_vec = a.to_vec + (b.to_vec + c.to_vec) := rfl,
    rw [p1,p2],
    cc
    }
end


instance add_semigroup_vectr : add_semigroup (vectr s) := ⟨ add_vectr_vectr s, add_assoc_vectr s⟩ 

@[simp]
def vectr_zero := @mk_vectr K _ _ n f s (0:K)
instance has_zero_vectr : has_zero (vectr s) := ⟨vectr_zero s⟩

#check mul_zero_class.zero

lemma zero_add_vectr : ∀ a : vectr s, 0 + a = a := 
begin
    intros,--,ext,
    cases a,
    generalize h0 : (0:vectr s) = tmp,
    cases tmp,

    have h1 : ({to_vec := tmp} : vectr s) + ({to_vec := a} : vectr s)= {to_vec := tmp + a} := rfl,
    simp * at *,
    dsimp [has_zero.zero, mul_zero_class.zero, monoid_with_zero.zero,semiring.zero,ring.zero,division_ring.zero] at h0,
    --cases h0,
    cases tmp,
    have h2: ({to_prod := tmp__to_prod, inv := tmp_inv}:vec K) = {to_prod := (field.zero , field.zero ), inv := rfl} 
            := by cc,
    simp * at *,
    dsimp [has_zero.zero, mul_zero_class.zero, monoid_with_zero.zero,add_monoid.zero, sub_neg_monoid.zero, add_group.zero, semiring.zero,ring.zero,division_ring.zero],
    trivial,
end

lemma add_zero_vectr : ∀ a : vectr s, a + 0 = a := 
begin
    intros,ext,
    exact add_zero _,
    exact add_zero _,
end

instance add_monoid_vectr : add_monoid (vectr s) := ⟨ 
    -- add_semigroup
    add_vectr_vectr s, 
    add_assoc_vectr s, 
    -- has_zero
    vectr_zero s,
    -- new structure 
    zero_add_vectr s, 
    add_zero_vectr s
⟩

instance has_neg_vectr : has_neg (vectr s) := ⟨ neg_vectr s ⟩
instance has_sub_vectr : has_sub (vectr s) := ⟨ sub_vectr_vectr s ⟩ 
lemma sub_eq_add_neg_vectr : ∀ a b : vectr s, a - b = a + -b := 
begin
    intros,ext,
    refl,refl

end 


instance sub_neg_monoid_vectr : sub_neg_monoid (vectr s) := ⟨ 
    add_vectr_vectr s, add_assoc_vectr s, vectr_zero s, zero_add_vectr s, add_zero_vectr s, -- add_monoid
    neg_vectr s,                                                                  -- has_neg
    sub_vectr_vectr s,                                                              -- has_sub
    sub_eq_add_neg_vectr s,                                                       -- new
⟩ 

lemma add_left_neg_vectr : ∀ a : vectr s, -a + a = 0 := 
begin
    intros,
    ext,
    repeat {
    have h0 : (-a + a).to_vec = -a.to_vec + a.to_vec := rfl,
    simp [h0],
    have : (0:vec K) = (0:vectr s).to_vec := rfl,
    simp *,
    }
    
end


instance : add_group (vectr s) := ⟨
    -- sub_neg_monoid
    add_vectr_vectr s, add_assoc_vectr s, vectr_zero s, zero_add_vectr s, add_zero_vectr s, -- add_monoid
    neg_vectr s,                                                                  -- has_neg
    sub_vectr_vectr s,                                                              -- has_sub
    sub_eq_add_neg_vectr s, 
    -- new
    add_left_neg_vectr s,
⟩ 

lemma add_comm_vectr : ∀ a b : vectr s, a + b = b + a := 
begin
    intros,
    ext,
    repeat {
    have p1 : (a + b).to_vec = a.to_vec + b.to_vec:= rfl,
    have p2 : (b + a).to_vec = b.to_vec + a.to_vec := rfl,
    rw [p1,p2],
    cc
    }    
end

instance add_comm_semigroup_vectr : add_comm_semigroup (vectr s) := ⟨
    -- add_semigroup
    add_vectr_vectr s, 
    add_assoc_vectr s,
    add_comm_vectr s,
⟩

instance add_comm_monoid_vectr : add_comm_monoid (vectr s) := ⟨
-- add_monoid
    -- add_semigroup
    add_vectr_vectr s, 
    add_assoc_vectr s, 
    -- has_zero
    vectr_zero s,
    -- new structure 
    zero_add_vectr s, 
    add_zero_vectr s,
-- add_comm_semigroup (minus repeats)
    add_comm_vectr s,
⟩

instance has_scalar_vectr : has_scalar K (vectr s) := ⟨
smul_vectr s,
⟩

lemma one_smul_vectr : ∀ b : vectr s, (1 : K) • b = b := begin
    intros,ext,
    repeat {
        have h0 : ((1:K) • b).to_vec = ((1:K)•(b.to_vec)) := rfl,
        rw [h0],
        simp *,
    }
end

lemma mul_smul_vectr : ∀ (x y : K) (b : vectr s), (x * y) • b = x • y • b :=
begin
    intros,
    cases b,
    ext,
    exact mul_assoc x y _,
    exact mul_assoc x y _
end

instance mul_action_vectr : mul_action K (vectr s) := ⟨
one_smul_vectr s,
mul_smul_vectr s,
⟩ 

lemma smul_add_vectr : ∀(r : K) (x y : vectr s), r • (x + y) = r • x + r • y := begin
    intros, ext,
    repeat {
    have h0 : (r • (x + y)).to_vec = (r • (x.to_vec + y.to_vec)) := rfl,
    have h1 : (r•x + r•y).to_vec = (r•x.to_vec + r•y.to_vec) := rfl,
    rw [h0,h1],
    simp *,
    }

end

lemma smul_zero_vectr : ∀(r : K), r • (0 : vectr s) = 0 := begin
    intros, ext, exact mul_zero _, exact mul_zero _
end
instance distrib_mul_action_K_vectrK : distrib_mul_action K (vectr s) := ⟨
smul_add_vectr s,
smul_zero_vectr s,
⟩ 

-- renaming vs template due to clash with name "s" for prevailing variable
lemma add_smul_vectr : ∀ (a b : K) (x : vectr s), (a + b) • x = a • x + b • x := 
begin
  intros,
  ext,
  exact right_distrib _ _ _,
  exact right_distrib _ _ _
end

lemma zero_smul_vectr : ∀ (x : vectr s), (0 : K) • x = 0 := begin
    intros,
    ext,
    exact zero_mul _, exact zero_mul _
end
instance semimodule_K_vectrK : semimodule K (vectr s) := ⟨ 
    add_smul_vectr s, 
    zero_smul_vectr s, 
⟩ 

instance add_comm_group_vectr : add_comm_group (vectr s) := ⟨
-- add_group
    add_vectr_vectr s, add_assoc_vectr s, vectr_zero s, zero_add_vectr s, add_zero_vectr s, -- add_monoid
    neg_vectr s,                                                                  -- has_neg
    sub_vectr_vectr s,                                                              -- has_sub
    sub_eq_add_neg_vectr s, 
    add_left_neg_vectr s,
-- commutativity
    add_comm_vectr s,
⟩

instance : vector_space K (vectr s) := semimodule_K_vectrK s

/-
    ********************
    *** Affine space ***
    ********************
-/

/-
Affine operations
-/
instance : has_add (vectr s) := ⟨add_vectr_vectr s⟩
instance : has_zero (vectr s) := ⟨vectr_zero s⟩
instance : has_neg (vectr s) := ⟨neg_vectr s⟩

/-
Lemmas needed to implement affine space API
-/
@[simp]
def sub_point_point (p1 p2 : point s) : vectr s := mk_vectr' s (p1.to_pt -ᵥ p2.to_pt)
@[simp]
def add_point_vectr {f : fm K n} {s : spc K f } (p : point s) (v : vectr s) : point s := 
    mk_point' s (v.to_vec +ᵥ p.to_pt) -- reorder assumes order is irrelevant
@[simp]
def add_vectr_point {f : fm K n} {s : spc K f } (v : vectr s) (p : point s) : point s := 
    mk_point' s (v.to_vec +ᵥ p.to_pt)

@[simp]
def aff_vectr_group_action : vectr s → point s → point s := add_vectr_point
instance : has_vadd (vectr s) (point s) := ⟨aff_vectr_group_action s⟩

lemma zero_vectr_vadd'_a1 : ∀ p : point s, (0 : vectr s) +ᵥ p = p := begin
    intros,
    ext,--exact zero_add _,
    exact add_zero _,
    exact add_zero _
end

lemma vectr_add_assoc'_a1 : ∀ (g1 g2 : vectr s) (p : point s), g1 +ᵥ (g2 +ᵥ p) = (g1 + g2) +ᵥ p := begin
    intros, ext,
    repeat {
    have h0 : (g1 +ᵥ (g2 +ᵥ p)).to_pt = (g1.to_vec +ᵥ (g2.to_vec +ᵥ p.to_pt)) := rfl,
    have h1 : (g1 + g2 +ᵥ p).to_pt = (g1.to_vec +ᵥ g2.to_vec +ᵥ p.to_pt) := rfl,
    rw [h0,h1],
    simp *,
    simp [has_vadd.vadd, has_add.add, add_semigroup.add, add_monoid.add, sub_neg_monoid.add, 
        add_group.add, distrib.add, ring.add, division_ring.add],
    cc,
    }
end

instance vectr_add_action: add_action (vectr s) (point s) := 
⟨ aff_vectr_group_action s, zero_vectr_vadd'_a1 s, vectr_add_assoc'_a1 s ⟩ 

@[simp]
def aff_point_group_sub : point s → point s → vectr s := sub_point_point s
instance point_has_vsub : has_vsub (vectr s) (point s) := ⟨ aff_point_group_sub s ⟩ 

instance : nonempty (point s) := ⟨mk_point s 0⟩

lemma point_vsub_vadd_a1 : ∀ (p1 p2 : (point s)), (p1 -ᵥ p2) +ᵥ p2 = p1 := begin
    intros, ext,
    repeat {
    have h0 : (p1 -ᵥ p2 +ᵥ p2).to_pt = (p1.to_pt -ᵥ p2.to_pt +ᵥ p2.to_pt) := rfl,
    rw h0,
    simp *,
    }
end

lemma point_vadd_vsub_a1 : ∀ (g : vectr s) (p : point s), g +ᵥ p -ᵥ p = g := 
begin
    intros, ext,
    repeat {
    have h0 : ((g +ᵥ p -ᵥ p) : vectr s).to_vec = (g.to_vec +ᵥ p.to_pt -ᵥ p.to_pt) := rfl,
    rw h0,
    simp *,
    }
end

instance aff_point_torsor : add_torsor (vectr s) (point s) := 
⟨ 
    aff_vectr_group_action s,
    zero_vectr_vadd'_a1 s,    -- from add_action
    vectr_add_assoc'_a1 s,    -- from add_action
    aff_point_group_sub s,    -- from has_vsub
    point_vsub_vadd_a1 s,     -- from add_torsor
    point_vadd_vsub_a1 s,     -- from add_torsor
⟩

open_locale affine
instance : affine_space (vectr s) (point s) := aff_point_torsor s

variables {f1 : fm K n} {f2 : fm K n} (s1 : spc K f1) (s2 : spc K f2)

--not usable?
abbreviation raw_tr := (pt K) ≃ᵃ[K] (pt K)
abbreviation fm_tr := (point s1) ≃ᵃ[K] (point s2)


/-
FIX THIS LATER
-/

def to_base_helper' : fm K n → @raw_tr K _ _
| (fm.base n) := ⟨
            ⟨   /-base case -/
                (λ p, p),
                (λ p, p),
                begin
                    unfold function.left_inverse,
                    intros,
                    simp *
                end,
                begin
                    unfold function.right_inverse function.left_inverse,
                    intros,
                    simp *
                end
            ⟩,
            ⟨
                (λ v, v),
                begin
                    intros, simp*
                end,
               -- (λ v, ⟨v.to_vec⟩),
                begin
                    intros, simp *
                end,
                (λ v, v),
                begin
                    unfold function.left_inverse,
                    intros, simp *
                end,
                begin
                    unfold function.left_inverse function.right_inverse,
                    intros, simp *
                end,
            ⟩,
            begin
                admit
            end
        ⟩
| (fm.deriv n c parent) := (⟨
            ⟨/-transform from current->parent-/
                λp, ⟨(p.to_prod.1*c.snd.to_prod.1 +  p.to_prod.2*c.fst.to_prod.1, 
                        p.to_prod.1*c.snd.to_prod.2 + p.to_prod.2*c.fst.to_prod.2),sorry⟩,
                let det := c.snd.to_prod.1*c.fst.to_prod.2 - c.snd.to_prod.2*c.fst.to_prod.1 in
                    λp, (⟨(p.to_prod.1*c.fst.to_prod.2/det - p.to_prod.2*c.fst.to_prod.1/det, 
                            -p.to_prod.1*c.snd.to_prod.2/det + p.to_prod.2*c.snd.to_prod.1/det),sorry⟩),
                sorry,
                sorry
            ⟩,
            ⟨
                λv, ⟨(v.to_prod.1, v.to_prod.2*c.snd.to_prod.2),begin 
                    cases v,
                    simp *,
                end⟩,
                sorry,
                sorry,
                λv, ⟨(v.to_prod.1, v.to_prod.2*c.snd.to_prod.2),begin 
                    cases v,
                    simp *,
                end⟩,
                sorry,
                sorry
            ⟩,
            sorry /-invert to parent->current and append to current->base-/
        ⟩ : @raw_tr K _ _).trans (to_base_helper' parent)

 
--change this to standard space
def spc.to_base (s1 : spc K f1) : @raw_tr K _ _ := to_base_helper' f1

/-
s1 

    i1              s2

        i2      i3
            b

-/

def spc.tr (s1 : spc K f1) {f2 : fm K n} : Π (s2 : spc K f2), (point s1) ≃ᵃ[K] (point s2) := 
    λ s2,
    let rawtr : @raw_tr K _ _ := s1.to_base.trans s2.to_base.symm in
                ⟨
            ⟨
                (λ p : point _, (⟨(rawtr p.1 : pt K)⟩ : point _)),
                (λ p : point _, (⟨(rawtr p.1 : pt K)⟩ : point _)),
                sorry,
                sorry
            ⟩,
            ⟨
                (λv : vectr _, (⟨(rawtr.linear v.1 : vec K)⟩ : vectr _)),
                sorry,
               -- (λ v, ⟨v.to_vec⟩),
                sorry,
                (λv : vectr _, (⟨(rawtr.linear v.1 : vec K)⟩ : vectr _)),
                sorry,
                sorry
            ⟩,
            sorry
        ⟩

variables (p1 : point s1) (v_1 : vectr s1)

def mytr := s1.tr s2

#check ((mytr s1 s2) p1) --point s2
#check (mytr s1 s2).linear v_1--matrix * [vec] //+- vec
#check 
#check



end implicitK

-- TODO: clean up naming in this file