/-
SCALAR_EXPR := (SCALAR_EXPR) | SCALAR_EXPR + SCALAR_EXPR | SCALAR_EXPR * SCALAR_EXPR | SCALAR_VAR | SCALAR_LITERAL
-/

def scalar := ℕ

structure scalar_var : Type :=
mk :: (index : ℕ)

def scalar_interp := scalar_var → scalar

def init_scalar_interp := λ (s : scalar_var), 0

inductive scalar_expression : Type 
| scalar_lit : ℕ → scalar_expression
| scalar_paren : scalar_expression → scalar_expression
| scalar_mul : scalar_expression → scalar_expression → scalar_expression
| scalar_add : scalar_expression → scalar_expression → scalar_expression
| scalar_var : scalar_var → scalar_expression

open scalar_expression

def e1 : scalar_expression := scalar_lit 3
def e2 : scalar_expression := scalar_paren e1
def e3 := scalar_add e1 e2
def e4 := scalar_mul e1 e2

def scalar_eval : scalar_expression → scalar_interp → scalar
| (scalar_lit n) i :=  n
| (scalar_paren e) i :=  scalar_eval e i
| (scalar_mul e1 e2) i := nat.mul (scalar_eval e1 i) (scalar_eval e2 i)
| (scalar_add e1 e2) i := nat.add (scalar_eval e1 i) (scalar_eval e2 i)
| (scalar_var v) i := i v

#reduce scalar_eval (scalar_lit 3) init_scalar_interp

/-
    VEC_EXPR := (VEC_EXPR) | VEC_EXPR + VEC_EXPR | VEC_EXPR * SCALAR_EXPR | VEC_VAR | VEC_LITERAL
-/

structure space : Type :=
mk :: (index : ℕ)

def bar_space := space.mk 0
def foo_space := space.mk 1

structure vector_variable : Type :=
mk :: (index : ℕ)

structure phys_vector : Type :=
mk :: (x y z : ℕ)

def vector_interp := vector_variable → phys_vector
def init_vector_interp := λ (s : vector_variable), phys_vector.mk 0 0 0

def v1 := phys_vector.mk 1 2 3
def v2 := phys_vector.mk 1 6 2
def v3 := phys_vector.mk 0 1 3
def v4 := phys_vector.mk 1 2 4

#reduce v1

inductive vector_space_transformation : Type

inductive vector_space_transformation_expressions : Type

inductive vector_expression : Type 
| vector_literal : phys_vector → vector_expression
| scalar_vector_mul : scalar_expression → vector_expression → vector_expression
| vector_paren : vector_expression → vector_expression 
| vector_mul : vector_expression → vector_expression → vector_expression
| vector_add : vector_expression → vector_expression → vector_expression
| vector_var : vector_variable → vector_expression

open vector_expression

def vector_eval : vector_expression → vector_interp → scalar_interp → phys_vector
| (vector_literal v) i_v i_s :=  v
| (scalar_vector_mul s v) i_v i_s :=
    begin
        have interp_v := vector_eval v i_v i_s,
        have interp_s := scalar_eval s i_s,
        exact (phys_vector.mk 
            (interp_v.x * interp_s)
            (interp_v.y * interp_s)
            (interp_v.z * interp_s)
        ),
    end
| (vector_paren v) i_v i_s := vector_eval v i_v i_s
| (vector_mul e1 e2) iv is := phys_vector.mk 0 0 0 -- stub
| (vector_add e1 e2) i_v i_s := 
    begin
        have interp_v1 := vector_eval e1 i_v i_s,
        have interp_v2 := vector_eval e2 i_v i_s,
        exact (phys_vector.mk 
            (interp_v1.x + interp_v2.x)
            (interp_v1.y + interp_v2.y)
            (interp_v1.z + interp_v2.z)
        ),
    end
| (vector_var v) i_v i_s := i_v v

def ve1 : vector_expression := vector_literal v1
def ve2 : vector_expression := vector_add (vector_literal v2) (ve1)
def vv0 : vector_variable := vector_variable.mk 0
def vv1 : vector_variable := vector_variable.mk 1
def vv0_e : vector_expression := vector_paren (vector_var vv0)
def vv1_e : vector_expression := scalar_vector_mul (scalar_lit 3) (vector_var vv1) 

def v_interp : vector_interp :=
    λ v : vector_variable,
        match v.index with,
            0 := phys_vector.mk 1 1 1,
            1 := phys_vector.mk 2 2 2,
            _ := phys_vector.mk 0 0 0
        end

#reduce vector_eval (ve2) init_vector_interp init_scalar_interp
#reduce vector_eval (vector_add vv0_e vv1_e) v_interp init_scalar_interp