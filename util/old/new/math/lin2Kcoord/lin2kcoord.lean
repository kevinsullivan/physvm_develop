import algebra.module.basic
import linear_algebra.affine_space.affine_equiv

universes u 

variables (K : Type u) [field K] [inhabited K]

/-
Main goal of this file is to instsantiate this typeclass application.
-/
#check module K (K × K)

/-
Operations
-/

-- component-wise pair add already defined
#print prod.has_add
/-
  @[instance]
  protected def prod.has_add : Π {M : Type u_5} {N : Type u_6} [_inst_1 : has_add M] [_inst_2 : has_add N], has_add (M × N) :=
  λ {M : Type u_5} {N : Type u_6} [_inst_1 : has_add M] [_inst_2 : has_add N],
    {add := λ (p q : M × N), (p.fst + q.fst, p.snd + q.snd)}
-/

-- scalar multiplication scales each component
@[ext]
def smul : K → K × K → K × K
| a (f,s) := ⟨ a * f, a * s ⟩ 


/-
/-- Scalar multiplication operation, denoted `•` (`\bu`) -/
class has_scalar (α : Type u) (γ : Type v) := (smul : α → γ → γ)
infixr ` • `:73 := has_scalar.smul
-/
/-
3/27 Andrew commented out, duplicate
-/
--instance : has_scalar K (K × K) := ⟨ smul K ⟩ 

/-
class mul_action (α : Type u) (β : Type v) [monoid α] extends has_scalar α β :=
(one_smul : ∀ b : β, (1 : α) • b = b)
(mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b)
-/

#check one_mul
#check mul_assoc

lemma one_smul_l2 : ∀ v : K × K, (1 : K) • v = v := 
begin
  intros,
  cases v,
  ext,
  simp *,
  simp *
end
lemma mul_smul_l2 : ∀ (x y : K) (b : K × K), (x * y) • b = x • y • b := 
begin
  intros,
  ext,
  simp *,
  exact mul_assoc x y _,
  simp *,
  exact mul_assoc x y _,
end
--instance : mul_action K (K × K) := ⟨ one_smul_l2 K, mul_smul_l2 K ⟩ 



/-
class distrib_mul_action (α : Type u) (β : Type v) [monoid α] [add_monoid β]
  extends mul_action α β :=
(smul_add : ∀(r : α) (x y : β), r • (x + y) = r • x + r • y)
(smul_zero : ∀(r : α), r • (0 : β) = 0)
-/
lemma smul_add_l2 : ∀(r : K) (x y : K × K), r • (x + y) = r • x + r • y := 
begin
  intros,
  ext,
  simp *,
  simp *,
end
lemma smul_zero_l2 : ∀ (r : K), r • (0 : K × K) = 0 := 
begin
  intros,
  ext,
  simp *,
  simp *
end
--instance : distrib_mul_action K (K × K) := ⟨ smul_add_l2 K, smul_zero_l2 K⟩ 



/- 
class module (R : Type u) (M : Type v) [semiring R]
  [add_comm_monoid M] extends distrib_mul_action R M :=
(add_smul : ∀(r s : R) (x : M), (r + s) • x = r • x + s • x)
(zero_smul : ∀x : M, (0 : R) • x = 0)
-/
#check module
lemma add_smul_l2 : ∀ (r s : K) (x : K × K), (r + s) • x = r • x + s • x := 
begin
  intros,
  ext,
  simp *,
  exact right_distrib r s _,
  simp *,
  exact right_distrib r s _,
end
lemma zero_smul_l2 : ∀ (x : K × K), (0 : K) • x = 0 := 
begin
  intros,
  ext,
  simp *,
  simp *
end
instance module_K_KxK : module K (K × K) := ⟨ add_smul_l2 K, zero_smul_l2 K ⟩ 



/-
module : 
  Π (R : Type u_1)                -- ring of scalars
    (M : Type u_2)                -- set of vectoids
    [_inst_1 : field R]           -- implicit
    [_inst_2 : add_comm_group M], -- implicit
  Type (max u_1 u_2) :=
    module R M      -- a vector space R M is a module R M
-/

