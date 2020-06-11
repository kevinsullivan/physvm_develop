import data.real.basic
namespace peirce
inductive space : Type
| mk (id : ℕ) : space 
abbreviation scalar := ℝ
inductive vec : space → Type 
| mkVector : Π s : space, scalar → scalar → scalar → vec s
def vadd { s : space } (v1 v2 : vec s) : vec s :=
    vec.mkVector s 0 0 0 --stub
def vsmul {s : space } (n : scalar) (v1 : vec s) : vec s :=
    vec.mkVector s 0 0 0 --stub
def sadd : scalar → scalar → scalar
| _ _ := 0 --stub
def smul : scalar → scalar → scalar
| _ _ := 0 --stub
end peirce