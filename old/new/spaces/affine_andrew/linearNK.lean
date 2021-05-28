import linear_algebra.affine_space.basic
import algebra.module.basic
import tactic.linarith

import algebra.direct_sum

open_locale direct_sum

universes u 

variables 
{n1 : {n : ℕ // n > 0}} 
(n : ℕ)
(F : Type u) [ring F] [inhabited F] [field F] --added field for vector space


--def n1 := n + 1
/-
inductive prod_rec : ℕ → Type u
| maker {} : prod_rec 0
| starter {n :ℕ} (p : F × (prod_rec (n-1:ℕ))) : prod_rec n
-/
--Andrew
--having trouble with the following
--prod F (prod F (prod F (...)))
--how to write in closed form with guarantee of the sub
--however,
--as Dr. Sullivan has mentioned many times, direct sum and product are equivalent for finite
--and, we want to use direct sum somewhere, so why not here?


#check ⨁i: fin n, F


variables (p : ⨁i: fin n, F)

def hm : Π(i:fin n), F := λi, p i

#check p ⟨0,sorry⟩

variables (x : Πi:fin n,F) (ast : fin n)

def p3 : Πi:fin n,F := λ i, 0

def p5 : ⨁i: {n : ℕ // n > 0}, F := ↑(λ i:{n : ℕ // n > 0},0)

def p4 : ⨁i: fin n, F := ↑(λ i:fin n,(0:F) : Π(i:fin n),F)

def p8 : ⨁i: fin n, F := ()

/-
def mk (s : finset ι) : (Π i : (↑s : set ι), β i.1) →+ ⨁ i, β i :=
{ to_fun := dfinsupp.mk s,
  map_add' := λ _ _, dfinsupp.mk_add,
  map_zero' := dfinsupp.mk_zero, }
-/

#check finset

#check direct_sum.mk ↑x ⟨⟩

#check (↑(λ i : fin n, 0)  : ⨁i: fin n, F)

#check (↑(λ i : fin n, 0))

#check (direct_sum.mk ↑x ast (λ i, 0))


#check prod F (prod F F)
/-
inductive even : N → Prop
| zero : even 0
| add_two : ∀k : N, even k → even (k + 2)


inductive prod_rec: ℕ → Type u
| base {} (k : F) : prod_rec 0
| ind {n : ℕ} (pf : n > 0) : ∀k :ℕ,(prod F (@prod_rec k) →  prod_rec n

nested occurrence 'list.{0} (foo n)' contains variables that are not parameters
view this post on Zulip Mario Carneiro (Jan 03 2021 at 07:07):
This is called a nested inductive type, 
because you have the type you are defining inside the argument 
to another inductive type. Lean's support for nested inductives is 
extremely limited and I recommend you avoid them entirely. 
It's usually possible to rewrite things to avoid them, 
although that would require some more context 
-/

structure prod_rec 
    (n : ℕ) (ngz : 0 < n) (T : Type u) (T1 : Type u) (T2 : Type (max u 0)) (T3 : Type (max u 0)):=
  (pr : prod F T)
  (pf : T=(prod F T1))
  (t : (if n = 1 then T1=F else (if n=2 then (T=(prod F (prod F F))) else ( T=(prod F T2)))))
  --(t : (if n = 1 then T2=F else T=(prod F T2)))

/-
attribute [reducible]
def indexed.as_list_helper
    {F : Type u}
    {n : ℕ}
    [inhabited F] 
    [field F] 
    (coords : fin n → F)
    : fin n → list F
| ⟨nat.zero,p⟩ := [(coords ⟨nat.zero,p⟩)]
| ⟨nat.succ k,p⟩ := 
    --append current index to result of recursive step and return
    let kp : k < n := begin
      have h₁ : k < k.succ := begin
        rw eq.symm (nat.one_add k),
        simp only [nat.succ_pos', lt_add_iff_pos_left]
      end,
      apply has_lt.lt.trans,
      exact h₁,
      exact p
    end in
    let upd := [(coords ⟨k, kp⟩)] in
    have (⟨k, kp⟩ : fin n) < (⟨k.succ,p⟩ : fin n), from begin
      simp only [subtype.mk_lt_mk],
      rw eq.symm (nat.one_add k),
      simp only [nat.succ_pos', lt_add_iff_pos_left]
    end,
    --have t : a < (a + b), from sorry,
    (indexed.as_list_helper ⟨k,kp⟩)++upd --$ λ _, sorry
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λi, i.val)⟩]}
-/


def get_prod_type (F : Type u) [ring F] [inhabited F] [field F] : ℕ → Type u
| (nat.zero) := F
| (1) := (prod_rec F 1 (begin
  simp only [nat.succ_pos']
end) F F F F)
| (2) := (prod_rec F 2 (begin
  simp only [nat.succ_pos']
end) F F F F)
| (n+3) := 
  (prod_rec F (n+3) (by simp) F (get_prod_type (n+2)) (get_prod_type (n+1)) (get_prod_type (n)))
--using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λi, i.val)⟩]}

#check (3:ℕ) > 4

#check ((0 : ℕ).lt 3)
#check @has_lt.lt.trans ℕ _ 0 1 2 (by simp) (by simp)

#check has_lt.lt

variables {T : Type u} {T1 : Type u} {T2 : Type u}

#check nat.add_zero

#check zero_le (1 : ℕ)

/-
very difficult function to write with the above structure.
-/
def prod_rec.coords : ∀n : ℕ, ∀pf : 0 < n → (prod_rec F (n) (by simp *) T T1 T2 T3) :=
begin
  cases (T1=F:bool)
  { }
  { }
end



def ttt := 1

def ppp : finset ℕ := ↑(fin n)


def ww : ⨁i: fin n, F := ↑(λi:fin n, (0:F))

--a single property structure 
/-structure vec := 
(coords : ⨁i: fin (n1), F)
(pf : coords 0 = 0)
-/

--this doesn't really work well
attribute [reducible]
abbreviation linearN := ⨁i: fin n, F

--#check linearN n F 0

def p11 : linearN n F := ↑(λ i:fin n, 0)

variables (k1 : ⨁i: fin (n+1), F)

#check k1 0

#check multiset

variables (l : list (fin n))

def ms : multiset (fin n) := ↑l 

def fs : finset (fin n) := finset.mk (ms n l) sorry

variables (pit : Π(i:fin n),F)

def la :=  (λi, pit i)

def ds : ⨁i: fin n, F := direct_sum.mk ↑pit (fs n l) la

def la : ⨁i: fin n, F := ↑(pit)
/-

notation `↑`:max x:max := coe x

notation `⇑`:max x:max := coe_fn x

notation `↥`:max x:max := coe_sort x
-/

def p : ⨁i: fin n, F := ↑pit--direct_sum.mk (pit) (fs n l) 


variables {t : ℕ} (k2 : ⨁i: fin t, F) (i : fin t) (j : fin n)

#check (k2 i : F)

def pe2 : F := k2 i

--variables (k1 : )

def linN2_add' (ln1 : ⨁i: fin n, F) (ln2 : ⨁i: fin n, F): (⨁i: fin n, F) :=
  (λi : fin n, (ln1 i : F) : Π(i: fin n),F)


def linN2_add {n2 : ℕ} : ⨁i: fin n, F → ⨁i: fin n, F → ⨁i: fin n, F
| (ln1:⨁i: fin n, F) (ln2:⨁i: fin n, F) := ln2

def linN_add {n2 : ℕ} : ⨁i: fin (n2+1), F → ⨁i: fin (n2+1), F → ⨁i: fin (n2+1), F
| ln1 ln2 := ln1

def linN_scale : F → (linearN n1 F) → linearN n1 F
| a (f,s) := ⟨ a * f, a * s ⟩ 

def linN_neg : linearN n F → linearN n F
| (f,s) := ⟨ -1 * f, -1 * s ⟩ 

def linN_sub :  linearN n F → linearN n F → linearN n F
| l1 l2 := linN_add F l1 (linN_neg F l2) 

instance : has_add (linearN n F) := ⟨ linN_add F ⟩ 
instance : has_zero (linearN n F) := ⟨ (0,0) ⟩ 
instance : has_scalar F (linearN n F) := ⟨ linN_scale F ⟩ 
instance : has_neg (linearN n F) := ⟨ linN_neg F ⟩ 
instance : has_sub (linearN n F) := ⟨ linN_sub F ⟩
instance : add_comm_group (linearN n F) := sorry
instance : module F (linearN n F) := sorry
--instance : field F := sorry
instance : vector_space F (linearN n F) := sorry
-- instance : 2D vector_space ...


