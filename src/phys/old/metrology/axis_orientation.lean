import ...math.affine.affine_euclidean_space_lib

open euclidean
open eucl_lib
open aff_lib

namespace orientation

structure AxisOrientation (dim : ℕ) :=
  (or : affine_euclidean_orientation dim)

/-
In relation to a body the standard is:

x forward
y left
z up
For short-range Cartesian representations of geographic locations, use the east north up [5] (ENU) convention:

X east
Y north
Z up
To avoid precision problems with large float32 values, it is recommended to choose a nearby origin such as your system's starting position.

Suffix Frames
In the case of cameras, there is often a second frame defined with a "_optical" suffix. This uses a slightly different convention:

z forward
x right
y down
For outdoor systems where it is desirable to work under the north east down [6] (NED) convention, define an appropriately transformed secondary frame with the "_ned" suffix:

X north
Y east
Z down
-/

noncomputable
def NWU_basis : fin 3 → aff_vec_coord_tuple ℝ 3
| ⟨0,p⟩ := affine_coord_space.mk_tuple_vec ⟨[0,-1,0], rfl⟩
| ⟨1,p⟩ := affine_coord_space.mk_tuple_vec ⟨[1,0,0], rfl⟩
| ⟨2,p⟩ := affine_coord_space.mk_tuple_vec ⟨[0,0,1], rfl⟩
| ⟨_,p⟩ := affine_coord_space.mk_tuple_vec ⟨[1,1,1], rfl⟩

noncomputable
def NED_basis : fin 3 → aff_vec_coord_tuple ℝ 3
| ⟨0,p⟩ := affine_coord_space.mk_tuple_vec ⟨[0,1,0], rfl⟩
| ⟨1,p⟩ := affine_coord_space.mk_tuple_vec ⟨[1,0,0], rfl⟩
| ⟨2,p⟩ := affine_coord_space.mk_tuple_vec ⟨[0,0,-1], rfl⟩
| ⟨_, p⟩ := sorry

noncomputable
def ENU_basis : fin 3 → aff_vec_coord_tuple ℝ 3
| ⟨0,p⟩ := affine_coord_space.mk_tuple_vec ⟨[1,0,0], rfl⟩
| ⟨1,p⟩ := affine_coord_space.mk_tuple_vec ⟨[0,1,0], rfl⟩
| ⟨2,p⟩ := affine_coord_space.mk_tuple_vec ⟨[0,0,1], rfl⟩
| ⟨_, p⟩ := sorry

noncomputable
def NWU : AxisOrientation 3 :=
  ⟨⟨NWU_basis, sorry, sorry⟩⟩

noncomputable
def NED : AxisOrientation 3 := 
  ⟨⟨NED_basis, sorry, sorry⟩⟩

noncomputable
def ENU : AxisOrientation 3 :=
  ⟨⟨ENU_basis, sorry, sorry⟩⟩

end orientation