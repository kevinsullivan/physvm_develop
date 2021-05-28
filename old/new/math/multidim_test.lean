import linear_algebra.affine_space.affine_equiv
import algebra.direct_sum
import linear_algebra.direct_sum_module

universes u 
variables 
(K : Type u) 
[field K]
[inhabited K]

#check smul_eq_zero
#check smul_eq_zero.mp
#check sub_smul

/-
Export affine_space (vec K) (pt K) := aff_pt_torsor K,
with vector_space K (vec K) = semimodule K (vec K).
-/
open_locale big_operators
open direct_sum
open_locale direct_sum

--notation `⨁`α, β  := direct_sum α β 

/-
Objects
-/

-- 1-D *affine* K pt and vec objects rep'd by 2-D linear K tuples
@[ext]
structure pt extends K × K := (inv : fst = 1)
/-
What about for 3d?
-/
@[ext]
structure pt3 extends K × K × K × K := (inv : fst = 1) 
/-
what about for pt n
-/
@[ext] ptn extends K × K × K × ...?
/-
Trying to define this type
-/
def get_K_n_type : nat → Type u
| 0 := K
| (nat.succ n) := K × (get_K_n_type n)
/-
The resulting type, Type u, of course, can refer to an affine vector OR any other type in the same universe
-/



def get_K_n_type_no_head : nat → Type u
| 0 := punit
| (nat.succ n) := K × (get_K_n_type_no_head n)

/-
what should this definition even be?
-/
structure pt_K_n_struct : Type (u+1) :=
  (n : ℕ)
  (inner : K × Type)


/-
How can we use any of this?

get_K_n_type is Type u, it could be an affine vector or a structure modeling an umbrella
-/

def pt_K_n_struct.coords (s : pt_K_n_struct K) : (get_K_n_type K s.n) :=
  begin
    --impossible to write this function
  end



/-
Direct Sum
-/
variables (n : nat ) 


def helpme : multiset K := ⟦[1,2,3]⟧

def hel_ : multiset (fin n)  := ⟦[⟨1,sorry⟩]⟧
/-
def direct_sum.lmk (R : Type u) [semiring R] (ι : Type v) [dec_ι : decidable_eq ι] (M : ι → Type w) [Π (i : ι), add_comm_monoid (M i)] [Π (i : ι), module R (M i)] (s : finset ι) :
(Π (i : ↥↑s), M i.val) →ₗ[R] ⨁ (i : ι), M i
-/

/-

def direct_sum.mk {ι : Type v} [dec_ι : decidable_eq ι] (β : ι → Type w) [Π (i : ι), add_comm_monoid (β i)] (s : finset ι) :
(Π (i : ↥↑s), β i.val) →+ ⨁ (i : ι), β i
-/

#check finset


def map_ : fin n → Type u := λn_, K
instance allmnd : Π (i : fin n), add_comm_monoid ((λ (i : fin n), map_ K n i) i) := sorry
instance allmod : Π (i : fin n), semimodule K ((λ (i : fin n), map_ K n i) i) := sorry
def muln_ : multiset (fin n)  := ⟦[⟨1,sorry⟩]⟧

def fins_ : finset (fin n) := ⟨(muln_ n), sorry⟩
variables (a : fin n → K) (b: Π (i : (↑(fins_ n) : set (fin n))), map_ K n i.val)

def dsumcommg : ⨁ (i : fin n), map_ K n i := direct_sum.mk (map_ K n) (fins_ n) b
def dsummod : ⨁ (i : fin n), map_ K n i := direct_sum.lmk K (fin n) (map_ K n) (fins_ n) b

#check (md1 K n) b

#check direct_sum.lmk K (fin n) (map_ K n) (fins_ n)

def md2 := direct_sum.lmk K (fin n) (map_ K n) (fins_ n)

lemma b :  direct_sum _ (map_ K n) = (⨁i, (map_ K n) i) := rfl

def type_of_dsum : Type u := @direct_sum (fin n) (map_ K n) begin
  intros,
  let k := (map_ K n i),
  let h0 : k = K := rfl,
  let h1 : (map_ K n i) = K := rfl,
  rw h1,
  by apply_instance
end

variables (x y : direct_sum (fin n) (map_ K n) ) (p : fin n)

def xt : direct_sum _ (map_ K n) := 

def tt : (⨁(fin n), (map_ K n)) := x

def dsakl  : map_ K n p := x p

variables (k : K)

def dsssaaak := k•x

--example : (x p) = K := 

@[class]
structure  test :=
  (t : Π (i : fin n), add_comm_monoid ((λ (i : fin n), map_ K n i) i))

def ppt [Π (i : fin n), add_comm_monoid ((λ (i : fin n), map_ K n i) i)] : _ := ⨁i, (map_ K n) i 

#check ppt K n

variables (z : ppt K n) (j : fin n)

#check quot
#check setoid.r

def tester : map_ K n j := λ j : fin n, (z : (⨁i, (map_ K n))) j


abbreviation pts [Π (i : fin n), add_comm_monoid ((λ (i : fin n), map_ K n i) i)] := ⨁i, (map_ K n) i

universes v w u₁

variables (ι : Type v) [dec_ι : decidable_eq ι] (β : ι → Type w)
