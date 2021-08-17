import 
    .....math.affine.affine_coordinate_framed_space_lib
    .....math.affine.affine_coordinate_transform
    .....math.affine.affine_euclidean_space
    .....math.affine.affine_euclidean_space_lib
import ..metrology.dimensions 
import ..metrology.measurement
import ..metrology.axis_orientation
import data.real.basic

noncomputable theory
--open real_lib
open measurementSystem
open orientation
open aff_fr
open aff_lib
open aff_trans
open eucl_lib

structure euclideanGeometry3 : Type :=
mk :: 
    --(sp : aff_lib.affine_coord_space.standard_space ℝ 3) 
    (sp : eucl_lib.affine_euclidean_space.standard_space ℝ 3)
    (id : ℕ) -- id serves as unique ID for a given geometric space


attribute [reducible]
def euclideanGeometry3.build (id : ℕ) : euclideanGeometry3 :=
    ⟨affine_euclidean_space.mk_with_standard ℝ 3, id⟩

noncomputable def euclideanGeometry3.algebra : euclideanGeometry3 →  
     affine_euclidean_space.standard_space ℝ 3
| (euclideanGeometry3.mk sp n) := sp

structure euclideanGeometry3Scalar :=
mk ::
    (sp : euclideanGeometry3)
    (val : ℝ)

attribute [reducible]
def euclideanGeometry3Scalar.build
    (sp : euclideanGeometry3)
    (val : vector ℝ 1) := 
    euclideanGeometry3Scalar.mk sp (val.nth 1)



attribute [reducible]
def euclideanGeometry3Scalar.algebra 
    (s : euclideanGeometry3Scalar)
    := 
    s.val

structure euclideanGeometry3Vector :=
mk ::
    (sp : euclideanGeometry3)
    (coords : vector ℝ 3)

attribute [reducible]
def euclideanGeometry3Vector.build
    (sp : euclideanGeometry3)
    (coords : vector ℝ 3) :=
    euclideanGeometry3Vector.mk
        sp 
        --⟨[coord], by refl⟩
        coords


attribute [reducible]
def euclideanGeometry3Vector.algebra 
    (v : euclideanGeometry3Vector)
    := 
        (aff_lib.affine_coord_space.mk_coord_vec
        (euclideanGeometry3.algebra v.sp).1 
        v.coords)


structure euclideanGeometry3Point :=
mk ::
    (sp : euclideanGeometry3)
    (coords : vector ℝ 3)

attribute [reducible]
def euclideanGeometry3Point.build
    (sp : euclideanGeometry3)
    (coords : vector ℝ 3) :=
    euclideanGeometry3Point.mk
        sp 
        --⟨[coord], by refl⟩
        coords

attribute [reducible]
def euclideanGeometry3Point.algebra 
    (v : euclideanGeometry3Point)
    := 
        (aff_lib.affine_coord_space.mk_coord_point
        (euclideanGeometry3.algebra v.sp).1 
        v.coords)



abbreviation euclideanGeometry3Basis :=
    (fin 3) → euclideanGeometry3Vector

inductive euclideanGeometry3Frame : Type
| std 
    (sp : euclideanGeometry3)
    : euclideanGeometry3Frame
| derived 
    (sp : euclideanGeometry3) --ALERT : WEAK TYPING
    (fr : euclideanGeometry3Frame) --ALERT : WEAK TYPING
    (origin : euclideanGeometry3Point)
    (basis : euclideanGeometry3Basis)
    (m : MeasurementSystem)
    (or : AxisOrientation 3)
    : euclideanGeometry3Frame
| interpret
    (fr : euclideanGeometry3Frame)
    (m : MeasurementSystem)
    (or : AxisOrientation 3)

attribute [reducible]
def euclideanGeometry3Frame.space : euclideanGeometry3Frame → euclideanGeometry3
| (euclideanGeometry3Frame.std sp) := sp
| (euclideanGeometry3Frame.derived s f o b m or) :=  s
| (euclideanGeometry3Frame.interpret f m o) := euclideanGeometry3Frame.space f

attribute [reducible]
def euclideanGeometry3Basis.build : euclideanGeometry3Vector → euclideanGeometry3Vector → euclideanGeometry3Vector → euclideanGeometry3Basis
| v1 v2 v3 := λi, if i = 1 then v1 else (if i = 2 then v2 else v3)

attribute [reducible]
def euclideanGeometry3Frame.build_derived
   : euclideanGeometry3Frame → euclideanGeometry3Point → euclideanGeometry3Basis → MeasurementSystem → AxisOrientation 3 → euclideanGeometry3Frame
| (euclideanGeometry3Frame.std sp) p v m or := euclideanGeometry3Frame.derived sp (euclideanGeometry3Frame.std sp) p v m or
| (euclideanGeometry3Frame.derived s f o b m or) p v ms or_ :=  euclideanGeometry3Frame.derived s (euclideanGeometry3Frame.derived s f o b m or) p v ms or
| (euclideanGeometry3Frame.interpret f m o) p v ms or :=  euclideanGeometry3Frame.derived (euclideanGeometry3Frame.space f) (euclideanGeometry3Frame.interpret f m o) p v ms or

attribute [reducible]
def euclideanGeometry3Frame.build_derived_from_coords
    : euclideanGeometry3Frame → vector ℝ 3 → vector ℝ 3 → vector ℝ 3 → vector ℝ 3 → 
        MeasurementSystem → AxisOrientation 3 → euclideanGeometry3Frame
| f or v1 v2 v3 m ax := 
    let s := euclideanGeometry3Frame.space f in
    (euclideanGeometry3Frame.build_derived f (euclideanGeometry3Point.build s or) 
        (euclideanGeometry3Basis.build (euclideanGeometry3Vector.build s v1) 
                                        (euclideanGeometry3Vector.build s v1) 
                                        (euclideanGeometry3Vector.build s v1)) m ax)


attribute [reducible]
noncomputable def euclideanGeometry3Frame.algebra :
    euclideanGeometry3Frame → aff_fr.affine_coord_frame ℝ 3
| (euclideanGeometry3Frame.std sp) := 
    aff_lib.affine_coord_space.frame 
        (euclideanGeometry3.algebra sp).1
| (euclideanGeometry3Frame.derived s f o b m or) :=
    let base_fr := (euclideanGeometry3Frame.algebra f) in
        let base_sp := 
            aff_lib.affine_coord_space.mk_from_frame base_fr in
                aff_lib.affine_coord_space.mk_frame
                    base_sp
                    (aff_lib.affine_coord_space.mk_coord_point base_sp o.coords)
                    (aff_lib.affine_coord_space.mk_basis base_sp 
                      ⟨[aff_lib.affine_coord_space.mk_coord_vec base_sp ((b 1)).coords,
                      aff_lib.affine_coord_space.mk_coord_vec base_sp ((b 2)).coords,
                      aff_lib.affine_coord_space.mk_coord_vec base_sp ((b 3)).coords], by refl⟩)
        base_fr 
| (euclideanGeometry3Frame.interpret f m o) := euclideanGeometry3Frame.algebra f

attribute [reducible]
def euclideanGeometry3.stdFrame (sp : euclideanGeometry3)
    := euclideanGeometry3Frame.std sp


structure euclideanGeometry3CoordinateVector
    extends euclideanGeometry3Vector :=
mk ::
    (frame : euclideanGeometry3Frame) 

attribute [reducible]
def euclideanGeometry3CoordinateVector.build
    (sp : euclideanGeometry3)
    (fr : euclideanGeometry3Frame)
    (coords : vector ℝ 3) :
    euclideanGeometry3CoordinateVector :=
    {
        frame := fr,
        ..(euclideanGeometry3Vector.build sp coords)
    }

attribute [reducible]
def euclideanGeometry3CoordinateVector.fromalgebra
    {f : affine_coord_frame ℝ 3}
    (sp : euclideanGeometry3)
    (fr : euclideanGeometry3Frame)
    (vec : aff_coord_vec ℝ 3 f)
    --(vec : aff_coord_vec ℝ 1 (euclideanGeometry3Frame.algebra fr))
    : euclideanGeometry3CoordinateVector
    := 
    euclideanGeometry3CoordinateVector.build sp fr (affine_coord_vec.get_coords vec)

attribute [reducible]
def euclideanGeometry3CoordinateVector.algebra 
    (v : euclideanGeometry3CoordinateVector)
    := 
        let base_fr := (euclideanGeometry3Frame.algebra v.frame) in
        let base_sp := 
            aff_lib.affine_coord_space.mk_from_frame base_fr in
                aff_lib.affine_coord_space.mk_coord_vec
                    base_sp
                    v.coords



structure euclideanGeometry3CoordinatePoint 
    extends euclideanGeometry3Point :=
mk ::
    (frame : euclideanGeometry3Frame) 

attribute [reducible]
def euclideanGeometry3CoordinatePoint.build
    (sp : euclideanGeometry3)
    (fr : euclideanGeometry3Frame)
    (coords : vector ℝ 3) :
    euclideanGeometry3CoordinatePoint :=
    {
        frame := fr,
        ..(euclideanGeometry3Point.build sp coords)
    }

attribute [reducible]
def euclideanGeometry3CoordinatePoint.fromalgebra
    {f : affine_coord_frame ℝ 3}
    (sp : euclideanGeometry3)
    (fr : euclideanGeometry3Frame)
    (pt : aff_coord_pt ℝ 3 f)
    : euclideanGeometry3CoordinatePoint
    := 
    euclideanGeometry3CoordinatePoint.build sp fr (affine_coord_pt.get_coords pt)

attribute [reducible]
def euclideanGeometry3CoordinatePoint.algebra 
    (v : euclideanGeometry3CoordinatePoint)
    := 
        let base_fr := (euclideanGeometry3Frame.algebra v.frame) in
        let base_sp := 
            aff_lib.affine_coord_space.mk_from_frame base_fr in
                aff_lib.affine_coord_space.mk_coord_point
                    base_sp
                    v.coords

--attribute [reducible]
structure euclideanGeometry3Transform :=
    (sp : euclideanGeometry3)
    (from_ : euclideanGeometry3Frame)
    (to_ : euclideanGeometry3Frame)

def euclideanGeometry3Transform.build
    (sp : euclideanGeometry3)
    (from_ : euclideanGeometry3Frame)
    (to_ : euclideanGeometry3Frame)
    :=
    euclideanGeometry3Transform.mk sp from_ to_

def euclideanGeometry3Transform.fromalgebra
    (sp : euclideanGeometry3)
    (from_ : euclideanGeometry3Frame)
    (to_ : euclideanGeometry3Frame)
    (tr : affine_coord_frame_transform ℝ 3 (euclideanGeometry3Frame.algebra from_) (euclideanGeometry3Frame.algebra to_))
    :=
    euclideanGeometry3Transform.mk sp from_ to_

attribute [reducible]
def euclideanGeometry3Transform.algebra 
    (tr : euclideanGeometry3Transform)
    :=
    affine_coord_space.build_transform ℝ 3 ((euclideanGeometry3Frame.algebra tr.from_)) ((euclideanGeometry3Frame.algebra tr.to_))
        (⟨⟨⟩⟩ : affine_coord_space ℝ 3 
            _)
        (⟨⟨⟩⟩ : affine_coord_space ℝ 3 
            _)    

--attribute [reducible]
structure euclideanGeometry3Angle :=
    (sp : euclideanGeometry3)
    (val : vector ℝ 1)

def euclideanGeometry3Angle.build
    (sp : euclideanGeometry3)
    (val : vector ℝ 1)
    :=
    euclideanGeometry3Angle.mk sp val

def euclideanGeometry3Angle.fromalgebra
    (sp : euclideanGeometry3)
    (a: euclidean.affine_euclidean_space.angle) 
    :=
    euclideanGeometry3Angle.mk sp ⟨[a.val],rfl⟩

attribute [reducible]
def euclideanGeometry3Angle.algebra 
    (a : euclideanGeometry3Angle)
    : euclidean.affine_euclidean_space.angle
    :=
    ⟨a.val.nth 0⟩


--attribute [reducible]
structure euclideanGeometry3Orientation :=
    (sp : euclideanGeometry3)
    (o : eucl_lib.affine_euclidean_orientation 3)
   -- (val : vector ℝ 1)

def euclideanGeometry3Orientation.build
    (sp : euclideanGeometry3)
    --(o : eucl_lib.affine_euclidean_orientation 3)
    :=
    euclideanGeometry3Orientation.mk sp NWU.or

def euclideanGeometry3Orientation.fromalgebra
    (sp : euclideanGeometry3)
    (or: eucl_lib.affine_euclidean_orientation 3) 
    :=
    euclideanGeometry3Orientation.mk sp or

attribute [reducible]
def euclideanGeometry3Orientation.algebra 
    (a : euclideanGeometry3Orientation)
    : eucl_lib.affine_euclidean_orientation 3
    :=
    a.o

structure euclideanGeometry3Rotation :=
    (sp : euclideanGeometry3)
    (r : eucl_lib.affine_euclidean_rotation 3)
   -- (val : vector ℝ 1)

def euclideanGeometry3Rotation.build
    (sp : euclideanGeometry3)
   -- (val : vector ℝ 1)
    :=
    let or := NWU.or in
    euclideanGeometry3Rotation.mk sp ⟨or.1,or.2,or.3⟩

def euclideanGeometry3Rotation.fromalgebra
    (sp : euclideanGeometry3)
    (r : eucl_lib.affine_euclidean_rotation 3)
    :=
    euclideanGeometry3Rotation.mk sp r

attribute [reducible]
def euclideanGeometry3Rotation.algebra 
    (a : euclideanGeometry3Rotation)
    : eucl_lib.affine_euclidean_rotation 3
    :=
    a.r


/-
	(	(euclideanGeometry3Transform.algebra (
	let sp:= (euclideanGeometry3Eval (lang.euclideanGeometry3.spaceExpr.var ⟨⟨8⟩⟩) env382) in
	let domain_:= (euclideanGeometry3FrameEval (lang.euclideanGeometry3.frameExpr.var ⟨⟨20⟩⟩) env382) in
	let codomain_:= (euclideanGeometry3FrameEval (lang.euclideanGeometry3.frameExpr.var ⟨⟨16⟩⟩) env382) in
	(euclideanGeometry3Transform.build sp domain_ codomain_ )
)) 
) (	(euclideanGeometry3CoordinatePoint.algebra (
(euclideanGeometry3CoordinatePointEval (lang.euclideanGeometry3.CoordinatePointExpr.var ⟨⟨4⟩⟩) env382)
))
) 
-/

variables 
    (sp1 : euclideanGeometry3)
    (fr1 : euclideanGeometry3Frame)
    (fr2 : euclideanGeometry3Frame)
    (pt : euclideanGeometry3Point)
    (tr : euclideanGeometry3Transform)

#check 
    (euclideanGeometry3Transform.algebra tr) 


#check 
	(	(euclideanGeometry3Transform.algebra (
	let sp:= (euclideanGeometry3Eval (lang.euclideanGeometry3.spaceExpr.var ⟨⟨8⟩⟩) env382) in
	let domain_:= (euclideanGeometry3FrameEval (lang.euclideanGeometry3.frameExpr.var ⟨⟨20⟩⟩) env382) in
	let codomain_:= (euclideanGeometry3FrameEval (lang.euclideanGeometry3.frameExpr.var ⟨⟨16⟩⟩) env382) in
	(euclideanGeometry3Transform.build sp domain_ codomain_ )
)) 
) (	(euclideanGeometry3CoordinatePoint.algebra (
(euclideanGeometry3CoordinatePointEval (lang.euclideanGeometry3.CoordinatePointExpr.var ⟨⟨4⟩⟩) env382)
))
) 

variables (x : )