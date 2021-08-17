import ..lin2Kcoord.lin2kcoord
import linear_algebra.direct_sum_module

universes u 
variables 
(K : Type u) 
[field K]
[inhabited K]

/-
We represent primitive points and vectors constituting a 1-D affine 
space with a field K by as elements of a 2-D linear space over K. We
represent the 1-D affine point, p, with coordinate x : K, as a pair, 
(1 : K, x), and a 1-D (affine space) vector, v, with coordinate, x : K,
as a pair (0 : K, x). 

We prove the following properties

- vector-vector addition
- scalar-vector multiplication
- vector negation
- vector subtraction
- zero vector

- piont-point subtraction
- point-vector addition

- vectors act on points by point-vector addition
- subtraction of points yields vectors in a specific way
- etc. need to explain proof in structured English to make it comprehensible 
- ...

SULLIVAN: Can we now do away with the lin2K stuff and just
use Lean's type system to distinguish single-coordinate pts
from single-coordinate vecs?
-/

/-
Objects: 
- pt, point in a 1-D affine space over field K
- vec, vector in a 1-D affine space over field K
-/
@[ext]
structure pt := (coord : K)

@[ext]
structure vec := (coord : K)

@[simp]
def mk_pt (k : K) : pt K  := ⟨k⟩             -- exported

@[simp]
def mk_vec (k : K) : vec K := ⟨k⟩            -- exported

/-
    *******************************
    *** Vector space operations ***
    *******************************
-/


@[simp]
def add_vec_vec (v1 v2 : vec K) : vec K := ⟨v1.coord + v2.coord⟩

@[simp]
def smul_vec (k : K) (v : vec K) : vec K := ⟨k*v.coord⟩

@[simp]
def neg_vec (v : vec K) : vec K := ⟨-v.coord⟩

@[simp]
def sub_vec_vec (v2 v1 : vec K) : vec K := add_vec_vec K v2 (neg_vec K v1)  -- v2-v1

@[simp]
def vec_zero  := mk_vec K 0

instance : has_zero (vec K) := ⟨vec_zero K⟩
instance : has_neg (vec K) := ⟨neg_vec K⟩


/-
    *******************************
    *** Affine space operations ***
    *******************************
-/

@[simp]
def sub_pt_pt (p1 p2 : pt K) : vec K := ⟨p1.coord - p2.coord⟩

@[simp]
def add_pt_vec (p : pt K) (v : vec K) : pt K := ⟨p.coord + v.coord⟩

@[simp]
def add_vec_pt (v : vec K) (p : pt K) : pt K := ⟨p.coord + v.coord⟩
-- add affine combination operation here 

@[simp]
def aff_vec_group_action := add_vec_pt K

@[simp]
def aff_pt_group_sub := sub_pt_pt K

instance : has_vadd (vec K) (pt K) := ⟨aff_vec_group_action K⟩
instance : has_vsub (vec K) (pt K) := ⟨ aff_pt_group_sub K ⟩ 

open_locale affine

@[simp]
def nsmul_vec : ℕ → (vec K) → (vec K) 
| nat.zero v := vec_zero K
| (nat.succ n) v := (add_vec_vec _) v (nsmul_vec n v)

@[simp]
def gsmul_vec : ℤ → (vec K) → (vec K) 
| (int.of_nat i) v := nsmul_vec K i v
| (int.neg_succ_of_nat i) v := (-(nsmul_vec K i v))

instance : has_add (vec K) := ⟨add_vec_vec K⟩

instance : add_comm_monoid (vec K) :=
⟨
    add_vec_vec K,
    begin
        intros,
        --dsimp [has_add.add, add_vec_vec, mk_vec', distrib.add, ring.add, division_ring.add, field.add],
        cases a,
        cases b,
        cases c,
        simp *,
        cc
    end,
    vec_zero K,
    begin
        intros,
        ext,
        exact zero_add _
    end,
    begin
        intros,
        ext,
        exact add_zero _,
    end,
    nsmul_vec K,
    begin
        simp [auto_param],
        dsimp [0, vec_zero K],
        ext,
        cc,
    end,
    begin
        simp [auto_param],
        intros,
        ext,
        simp *,
        cc,
    end,
    begin
        intros,
        ext,
        exact add_comm _ _,
    end,
⟩

instance : add_monoid (vec K) := 
⟨
add_vec_vec K,
begin
    intros,
    dsimp [has_add.add, add_vec_vec, distrib.add, ring.add, division_ring.add, field.add],
    cases a,
    cases b,
    cases c,
    simp *,
    cc
end,
vec_zero K,
begin
    intros,

    ext,
    exact zero_add _,
end,
begin
    intros,

    ext,
    exact add_zero _,
end,
nsmul_vec K
⟩

instance : sub_neg_monoid (vec K) := {
neg := (neg_vec K),
..(show add_monoid (vec K), by apply_instance),

}

--#check neg

instance : add_group (vec K) := {
add_left_neg := begin
    intros,
    --let h0 : (-a + a).to_prod = (-a).to_prod + a.to_prod := rfl,
    --let h1 : (0 : vec K).to_prod.fst = 0 := rfl,
    /-let h2 : (-a).to_prod = -a.to_prod := begin
        ext,
        simp *,
        let h3 : a.to_prod.fst = 0 := by exact a.inv,
        let h4 : (-a.to_prod.fst) = 0 := begin
            rw h3,
            exact neg_zero,
        end, 
        rw h4,
        exact (-a).inv,
        cases a,
        simp *,
        dsimp [has_neg.neg, sub_neg_monoid.neg, add_group.neg],
        let h5 : add_comm_group.neg 1 * a__to_prod.snd = -a__to_prod.snd := by exact neg_one_mul _,
        simp [h5],
        trivial
    end,
    -/
    /-ext,
    rw [h0],
    rw h1,
    rw h2,
    simp *,
    rw [h0],
    rw h2,
    simp *,
    let h6 : (0 : vec K).to_prod.snd = 0 := rfl,
    simp *,-/
    ext,
    let h0 : (-a + a).coord = (-a).coord + a.coord := rfl,
    simp *,
    dsimp [has_neg.neg, sub_neg_monoid.neg, add_group.neg],
    exact neg_add_self _,
end,
..(show sub_neg_monoid (vec K), by apply_instance),
}

instance : add_comm_group (vec K) :={
    add_comm := begin
        intros,
        ext,
        exact add_comm _ _,
    end,
..(show add_group (vec K), by apply_instance)
}

instance : has_scalar K (vec K) := ⟨ smul_vec K ⟩

instance : mul_action K (vec K) := 
⟨
begin
    intros,
    cases b,
    ext,
    exact one_mul _,
end, 
begin
    intros,
    cases b,
    ext,
    exact mul_assoc x y _,
end,
⟩

lemma left_distrib_K_vecK : ∀ (r : K) (x y : vec K), r • (x + y) = r • x + r • y := begin
intros,
        ext,
        exact left_distrib _ _ _,
end

instance : distrib_mul_action K (vec K) := 
⟨
    begin
        exact left_distrib_K_vecK K,
    end, 
    begin
    intros, ext, exact mul_zero _,
    end
⟩

lemma right_distrib_K_vecK : ∀ (r s : K) (x : vec K), (r + s) • x = r • x + s • x := begin
  intros,
  ext,
  exact right_distrib _ _ _,


end

instance : module K (vec K) := ⟨
begin
    exact right_distrib_K_vecK K
end,
begin
    intros,
    ext,
    exact zero_mul _,
end
⟩

lemma pt_sub_add_cancel : ∀ (p1 p2 : pt K), p1 -ᵥ p2 +ᵥ p2 = p1 := 
begin
    intros,
    ext,
    dsimp [has_vsub.vsub, has_vadd.vadd],
    
    suffices s1 : 0 + p1.coord + (p2.coord - p1.coord) = 0 + p2.coord,
    from begin
        simp *,
    end,
    exact add_add_sub_cancel 0 p2.coord p1.coord,
end


lemma zero_vec_vadd'_a1 : ∀ p : pt K, (0 : vec K) +ᵥ p = p := 
begin
    intros,
    ext,
    exact add_zero _,
end

#check add_assoc
instance : add_action (vec K) (pt K) :=
⟨
begin
    exact zero_vec_vadd'_a1 K
end,
begin
    intros,
    ext,
    dsimp [has_vadd.vadd],--, has_add.add],

    let : (g₁ + g₂).coord = g₁.coord + g₂.coord := rfl,
    simp *,
    let s1 : p.coord + g₂.coord + g₁.coord = p.coord + (g₁.coord + g₂.coord) :=
    begin
        let t1 : _:=  add_assoc p.coord g₂.coord g₁.coord,
        let t2 : g₂.coord + g₁.coord = g₁.coord + g₂.coord := by cc,
        rw t2.symm,
        exact t1,
    end,
    simp [s1],
end
⟩

instance : nonempty (pt K) := ⟨mk_pt K 1⟩

instance vecK_ptK_affine_space : affine_space (vec K) (pt K) := ⟨
    pt_sub_add_cancel K,
    begin
        intros,
        ext,
        simp [has_vadd.vadd, has_vsub.vsub],
    end,
⟩
