import .expr_base
--import ...math.aff1Kcoord.aff1Kcoord_std
import ...phys.time.time


namespace lang.time
universes u

variables (K : Type u) [field K] [inhabited K] {f : fm K TIME} {sp : spc K f} {f1 : fm K TIME} {f2 : fm K TIME}
-- {K : Type u} [field K] [inhabited K] {f : fm K TIME}

/-
Duration
-/
structure duration_var {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f) extends var 

inductive duration_expr {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f) : Type u
| lit (v : duration sp) : duration_expr
| var (v : duration_var sp) : duration_expr

abbreviation duration_env {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f) := 
  duration_var sp → duration sp

abbreviation duration_eval {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f)  := 
  duration_env sp → duration_var sp → duration sp


/-
Time
-/
structure time_var {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f) extends var

inductive time_expr {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f) : Type u
| lit (p : time sp) : time_expr
| var (v : time_var sp) : time_expr

abbreviation time_env {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f)  := 
  time_var sp → time sp

abbreviation time_eval {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f)  := 
  time_env sp → time_var sp → time sp


/-
Transform
-/
structure transform_var {K : Type u} [field K] [inhabited K] 
  {f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2 : spc K f2) extends var

inductive transform_expr {K : Type u} [field K] [inhabited K] 
  {f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2 : spc K f2) : Type u
| lit (p : time.time_transform sp1 sp2) : transform_expr
| var (v : transform_var sp1 sp2) : transform_expr

abbreviation transform_env {K : Type u} [field K] [inhabited K] 
  {f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2 : spc K f2)  := 
  transform_var sp1 sp2 → time.time_transform sp1 sp2

abbreviation transform_eval  {K : Type u} [field K] [inhabited K] 
  {f1 : fm K TIME} {f2 : fm K TIME} (sp1 : spc K f1) (sp2 : spc K f2) := 
  transform_env sp1 sp2 → transform_var sp1 sp2 → time.time_transform sp1 sp2

/-
Overall environment
-/

--omitting transforms from environment for now, which will make
--env.env, cmd, and etc. , even more complicated in terms of types

structure env {K : Type u} [field K] [inhabited K] {f : fm K TIME} (sp : spc K f) :=
  (d : duration_env sp )
  (t : time_env sp )

def env.init : env sp :=
  ⟨
    (λv, ⟨mk_vectr sp 1⟩),
    (λv, ⟨mk_point sp 0⟩)
  ⟩
end lang.time

/---import .expr_base
--import data.real.basic
import .expr_base
--import ...math.aff1Kcoord.aff1Kcoord_std
import ...phys.time.time


namespace lang.time
universes u

variables (K : Type u) [field K] [inhabited K] {f : fm K TIME} {sp : spc K f} 

structure duration_var extends var 

structure time_var extends var

inductive duration_expr (sp : spc K f) : Type u
| lit (v : duration sp) : duration_expr
| var (v : duration_var) : duration_expr

abbreviation duration_env  := 
  duration_var → duration sp

abbreviation duration_eval := 
  @duration_env K _ _ f sp → duration_var → duration sp

inductive time_expr (sp : spc K f) : Type u
| lit (p : time sp) : time_expr
| var (v : time_var) : time_expr

abbreviation time_env  := 
  time_var → time sp

abbreviation time_eval := 
  @time_env K _ _ f sp → time_var → time sp

structure env :=
  (d : @duration_env K _ _ f sp )
  (t : @time_env K _ _ f sp )

def env.init : @env K _ _ f sp :=
  ⟨
    (λv, ⟨mk_vectr sp 1⟩),
    (λv, ⟨mk_point sp 0⟩)
  ⟩
end lang.time-/
