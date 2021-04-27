import algebra

#check has_one
#check semigroup
#check monoid

namespace alg

universe u



@[class]  
structure has_op (α : Type u) := 
(op : α → α → α)

@[instance]
def has_op_nat : has_op nat := ⟨ nat.mul ⟩ 



@[class]
structure ext_has_op (α : Type u) extends has_op α 

instance ext_has_op_nat : ext_has_op nat := ⟨ ⟩ 



-- my_ext_ext_has_op: optiplicative semigroup plus optiplicative one
@[class]
structure ext_ext_has_op (α : Type u) extends ext_has_op α

instance ext_ext_has_op_nat : ext_ext_has_op nat := ⟨ ⟩ 

--instance nat_one : my_has_one nat := ⟨ 1 ⟩ 

def get_op
  {α : Type u} 
  [m : ext_ext_has_op α] :
  α → α → α :=
m.op

#check get_op 3 3

def aop (α : Type u) [m : ext_ext_has_op α] : α → α → α := m.op

#eval @aop nat _ 3 3

def foo_op
  {α : Type u} 
  [m : ext_ext_has_op α] :
  α → α → α :=
m.op

#check @foo_op

#check foo_op 3 4
#eval foo_op 3 4


/-
-/
set_option trace.class_instances true
set_option class.instance_max_depth 1000


def foo_ox
  {α : Type u} 
  [m : ext_ext_has_op α] 
  (a : α) : α :=
  let mop := m.op in 
    mop a a

#check @foo_ox

#check foo_ox 3 
#eval foo_ox 3 



def mul_foldr 
  {α : Type u} 
  [m : ext_ext_has_op α] :
  list α → α 
| [] := m.one
| (h::t) := m.op 

/-
def add_foldr 
  {α : Type u} 
  [m : ext_ext_has_op α] :
  list α → α  
| [] := m.one
| (h::t) := m.op h (add_foldr t)

def add_foldr 
  {α : Type u} 
  [m : ext_ext_has_op α] :
  list α → α  
| [] := m.one
| (h::t) := m.op h (add_foldr t)


def add_foldr 
  {α : Type u} 
  [m : ext_ext_has_op α] :
  list α → α  
| [] := m.one
| (h::t) := m.op h (add_foldr t)
-/



/-
https://www.youtube.com/watch?v=mvmuCPvRoWQ
-/

end alg