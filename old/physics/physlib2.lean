import ......math.affine.aff_coord_space
import data.real.basic
 

noncomputable theory

/-
physicalDimension
time and distance are base types
can create derived types with the inverse and multiplication operations
-/
/-
second
metre
kilogram
ampere
kelvin	
mole
candela
/
683
 watt per steradian.
-/
inductive PhysDimension : Type
| SILit : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → PhysDimension
| SIAdd : PhysDimension → PhysDimension → PhysDimension
| SINeg : PhysDimension → PhysDimension

open PhysDimension

/-
Uses additive notation where multipicative is typical
-/
def dimensionless := PhysDimension.SILit 0 0 0 0 0 0 0
def meters := PhysDimension.SILit 0 1 0 0 0 0 0
def time := PhysDimension.SILit 1 0 0 0 0 0 0
def vel := SIAdd meters (SINeg time) 
def hertz := PhysDimension.SINeg time
def velocity := PhysDimension.SIAdd meters hertz

-- Should be able to prove this is an abelian group

-- CHANGE THIS TO R+?
inductive PhysUnit : Type
| ReferenceStandard : PhysUnit -- Imperial vs SI? Who defines "Standard"?
| ReferenceLit : PhysUnit → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → PhysUnit
| ReferenceAdd : PhysUnit → PhysUnit → PhysUnit
| ReferengeNeg : PhysUnit → PhysUnit

def si_standard := PhysUnit.ReferenceStandard

--structure PhysAffineSpace (d : physicalDimension) (dimension : ℕ) : Type :=
 --   mk :: (std_frame : affine_frame dimension) 

/-


structure PhysSpace (d : physicalDimension) (dimension : ℕ) : Type :=
    mk :: (std_frame : affine_frame dimension) 

variables (pt : Type*) (K : Type*) (vec : Type*) (dimension : ℕ)
[field K] [add_comm_group vec] [vector_space K vec]

structure PhysSpace' :=
(aff_pf : affine_space pt K vec)
(std_frame : affine_frame dimension) --needs to be refactored to be the math version

-/
/-
inductive PhysAffineSpace : ℕ → PhysDimension → PhysUnit → Type
| SpaceLiteral (space_dimension : ℕ) (physical_dimension : PhysDimension) (physical_units : PhysUnit) : 
    PhysAffineSpace space_dimension physical_dimension physical_units
-/
variables (pt : Type*) (vec : Type*)
[add_comm_group vec] [vector_space ℝ vec]

structure PhysScalar (dim : PhysDimension) :=
(scalar : ℝ)

structure PhysAffineSpace (n : ℕ) (dim : PhysDimension) (unit : PhysUnit) :=
(name : string)
(pf : affine_space pt ℝ vec)

def BuildPhysSpace (name : string) (space_dimension : ℕ) (physical_dimension : PhysDimension) (unit : PhysUnit) : 
    (PhysAffineSpace (aff_pt ℝ space_dimension) (aff_vec ℝ space_dimension) space_dimension physical_dimension unit) :=
        ⟨name, aff_coord_inst ℝ space_dimension⟩
/-
inductive PhysVectorSpace : ℕ → PhysDimension → PhysUnit → Type
| SpaceLiteral (space_dimension : ℕ) (physical_dimension : PhysDimension) (physical_units : PhysUnit) : 
    PhysVectorSpace space_dimension physical_dimension physical_units
-/
/-
inductive PhysAffineFrame {space_dimension : ℕ} {physical_dimension : PhysDimension} {physical_units : PhysUnit} : 
 PhysAffineSpace (aff_pt ℝ space_dimension) (aff_vec ℝ space_dimension) space_dimension physical_dimension physical_units →  Type
| Standard (sp : PhysAffineSpace (aff_pt ℝ space_dimension) (aff_vec ℝ space_dimension) space_dimension physical_dimension physical_units) :  
    PhysAffineFrame sp
| Derived (sp : PhysAffineSpace (aff_pt ℝ space_dimension) (aff_vec ℝ space_dimension) space_dimension physical_dimension physical_units) : 
    PhysAffineFrame sp → vector (aff_vec ℝ space_dimension) space_dimension → (aff_pt ℝ space_dimension) → PhysAffineFrame sp
-/
inductive PhysAffineFrame {space_dimension : ℕ} {physical_dimension : PhysDimension} {physical_units : PhysUnit} : 
 PhysAffineSpace (aff_pt ℝ space_dimension) (aff_vec ℝ space_dimension) space_dimension physical_dimension physical_units →  Type
| Standard (sp : PhysAffineSpace (aff_pt ℝ space_dimension) (aff_vec ℝ space_dimension) space_dimension physical_dimension physical_units) :  
    PhysAffineFrame sp
| Derived (sp : PhysAffineSpace (aff_pt ℝ space_dimension) (aff_vec ℝ space_dimension) space_dimension physical_dimension physical_units) : 
    PhysAffineFrame sp /-→ vector (aff_vec ℝ space_dimension) space_dimension → (aff_pt ℝ space_dimension)-/ → PhysAffineFrame sp

def PhysAffineFrame.GetAffineSpace {space_dimension : ℕ} {physical_dimension : PhysDimension} {physical_units : PhysUnit} {aff_sp : PhysAffineSpace (aff_pt ℝ space_dimension) (aff_vec ℝ space_dimension) space_dimension physical_dimension physical_units}
    : PhysAffineFrame aff_sp → PhysAffineSpace (aff_pt ℝ space_dimension) (aff_vec ℝ space_dimension) space_dimension physical_dimension physical_units
| _ := aff_sp
def PhysAffineSpace.GetStandardFrame {space_dimension : ℕ} {physical_dimension : PhysDimension} {physical_units : PhysUnit}
     (aff_sp : PhysAffineSpace (aff_pt ℝ space_dimension) (aff_vec ℝ space_dimension) space_dimension physical_dimension physical_units) :
        PhysAffineFrame aff_sp :=
        PhysAffineFrame.Standard aff_sp

inductive PhysVectorBasis (space_dimension : ℕ) (physical_dimension : PhysDimension) (physical_units : PhysUnit): Type
| Standard : PhysAffineSpace (aff_pt ℝ space_dimension) (aff_vec ℝ space_dimension) space_dimension physical_dimension physical_units → PhysVectorBasis
| Derived : PhysVectorBasis → vector (aff_vec ℝ space_dimension) space_dimension → PhysVectorBasis

inductive PhysVector {space_dimension : ℕ} {physical_dimension : PhysDimension} {physical_units : PhysUnit} : 
 PhysAffineSpace (aff_pt ℝ space_dimension) (aff_vec ℝ space_dimension) space_dimension physical_dimension physical_units →  Type
| AffineLiteral (aff_sp : PhysAffineSpace (aff_pt ℝ space_dimension) (aff_vec ℝ space_dimension) space_dimension physical_dimension physical_units) : 
        PhysAffineFrame aff_sp → (aff_vec ℝ space_dimension) → 
            PhysVector aff_sp

def BuildAffinePhysVector1 {physical_dimension : PhysDimension} {physical_units : PhysUnit}
   {aff_sp : PhysAffineSpace (aff_pt ℝ 1) (aff_vec ℝ 1) 1 physical_dimension physical_units}
    (aff_fr : PhysAffineFrame aff_sp) (x : ℝ ) : PhysVector aff_sp := 
    PhysVector.AffineLiteral aff_sp aff_fr (aff_vec.mk [0, x] rfl rfl)

def BuildAffinePhysVector3 {physical_dimension : PhysDimension} {physical_units : PhysUnit}
   {aff_sp : PhysAffineSpace (aff_pt ℝ 3) (aff_vec ℝ 3) 3 physical_dimension physical_units}
    (aff_fr : PhysAffineFrame aff_sp) (x y z : ℝ) : PhysVector aff_sp := 
    PhysVector.AffineLiteral aff_sp aff_fr (aff_vec.mk [0, x ,y ,z] rfl rfl)

inductive PhysPoint {space_dimension : ℕ} {physical_dimension : PhysDimension} {physical_units : PhysUnit} : 
 PhysAffineSpace (aff_pt ℝ space_dimension) (aff_vec ℝ space_dimension) space_dimension physical_dimension physical_units →  Type
| AffineLiteral (aff_sp : PhysAffineSpace (aff_pt ℝ space_dimension) (aff_vec ℝ space_dimension) space_dimension physical_dimension physical_units) : 
        PhysAffineFrame aff_sp → (aff_pt ℝ space_dimension) → 
            PhysPoint aff_sp


def BuildAffinePhysPoint1 {physical_dimension : PhysDimension} {physical_units : PhysUnit}
   {aff_sp : PhysAffineSpace (aff_pt ℝ 1) (aff_vec ℝ 1) 1 physical_dimension physical_units}
    (aff_fr : PhysAffineFrame aff_sp) (x : ℝ ) : PhysPoint aff_sp := 
    PhysPoint.AffineLiteral aff_sp aff_fr (aff_pt.mk [1, x] rfl rfl)

def BuildAffinePhysPoint3 {physical_dimension : PhysDimension} {physical_units : PhysUnit}
   {aff_sp : PhysAffineSpace (aff_pt ℝ 3) (aff_vec ℝ 3) 3 physical_dimension physical_units}
    (aff_fr : PhysAffineFrame aff_sp) (x y z : ℝ) : PhysPoint aff_sp := 
    PhysPoint.AffineLiteral aff_sp aff_fr (aff_pt.mk [1, x ,y ,z] rfl rfl)

/-
def BuildVectorOfVecsInner {dim : ℕ} (sz : ℕ) (current : ℕ) (v : vector (aff_vec ℝ dim) (sz - current)) : vector (aff_vec ℝ dim) (sz - current + 1) :=
    v.head_cons (aff_pt.mk [1, 0 ,0 ,0] rfl rfl)

def BuildVectorOfVecs (dim : ℕ) (sz : ℕ) : vector (aff_vec ℝ dim) sz
| BuildVectorOfVecsInner sz, 
-/


abbreviation EuclideanGeometrySpace (space_dimension : ℕ) := 
    PhysAffineSpace (aff_pt ℝ space_dimension) (aff_vec ℝ space_dimension) space_dimension meters si_standard
abbreviation EuclideanGeometryFrame {space_dimension : ℕ} (sp : EuclideanGeometrySpace space_dimension) :=
    PhysAffineFrame sp
abbreviation EuclideanGeometryVector {space_dimension : ℕ} (sp : EuclideanGeometrySpace space_dimension) :=
    PhysVector sp
abbreviation EuclideanGeometryPoint {space_dimension : ℕ} (sp : EuclideanGeometrySpace space_dimension) :=
    PhysPoint sp

def BuildEuclideanGeometrySpace (name : string) (space_dimension : ℕ) : EuclideanGeometrySpace space_dimension :=
    BuildPhysSpace name space_dimension meters si_standard
def BuildEuclideanGeometry3Space (name : string): EuclideanGeometrySpace 3 := 
    BuildPhysSpace name 3 meters si_standard
def GetEuclideanGeometryStandardFrame {space_dimension : ℕ} (sp : EuclideanGeometrySpace space_dimension) : EuclideanGeometryFrame sp :=
    PhysAffineFrame.Standard sp
def BuildEuclideanGeometryFrame {space_dimension : ℕ} {sp : EuclideanGeometrySpace space_dimension} : EuclideanGeometryFrame sp → EuclideanGeometryFrame sp
| (fr : EuclideanGeometryFrame sp) := PhysAffineFrame.Derived sp fr
def BuildEuclideanGeometry3Vector {sp : EuclideanGeometrySpace 3} (fr : PhysAffineFrame sp) (x y z : ℝ)
        : EuclideanGeometryVector sp :=
    BuildAffinePhysVector3 fr x y z
def BuildEuclideanGeometry3Point {sp : EuclideanGeometrySpace 3} (fr : PhysAffineFrame sp) (x y z : ℝ)
        : EuclideanGeometryPoint sp :=
    BuildAffinePhysPoint3 fr x y z

abbreviation ClassicalVelocitySpace (space_dimension : ℕ) := 
    PhysAffineSpace (aff_pt ℝ space_dimension) (aff_vec ℝ space_dimension) space_dimension velocity si_standard
abbreviation ClassicalVelocityFrame {space_dimension : ℕ} (sp : ClassicalVelocitySpace space_dimension) :=
    PhysAffineFrame sp
abbreviation ClassicalVelocityVector {space_dimension : ℕ} (sp : ClassicalVelocitySpace space_dimension) :=
    PhysVector sp

def BuildClassicalVelocitySpace (name : string) (space_dimension : ℕ) : ClassicalVelocitySpace space_dimension :=
    BuildPhysSpace name space_dimension velocity si_standard
def BuildClassicalVelocity3Space (name : string) : ClassicalVelocitySpace 3 := 
    BuildPhysSpace name 3 velocity si_standard
def GetClassicalVelocityStandardFrame {space_dimension : ℕ} (sp : ClassicalVelocitySpace space_dimension) : ClassicalVelocityFrame sp :=
    PhysAffineFrame.Standard sp
def BuildClassicalVelocityFrame {space_dimension : ℕ} {sp : ClassicalVelocitySpace space_dimension} : ClassicalVelocityFrame sp → ClassicalVelocityFrame sp
| (fr : ClassicalVelocityFrame sp) := PhysAffineFrame.Derived sp fr
def BuildClassicalVelocity3Vector {sp : ClassicalVelocitySpace 3} (fr : PhysAffineFrame sp) (x y z : ℝ)
        : ClassicalVelocityVector sp :=
    BuildAffinePhysVector3 fr x y z

abbreviation ClassicalTimeSpace := 
    PhysAffineSpace (aff_pt ℝ 1) (aff_vec ℝ 1) 1 time si_standard
abbreviation ClassicalTimeFrame (sp : ClassicalTimeSpace) :=
    PhysAffineFrame sp
abbreviation ClassicalTimeVector (sp : ClassicalTimeSpace) :=
    PhysVector sp
abbreviation ClassicalTimePoint (sp : ClassicalTimeSpace) :=
    PhysPoint sp

def BuildClassicalTimeSpace (name : string) : ClassicalTimeSpace := 
    BuildPhysSpace name 1 time si_standard
def GetClassicalTimeStandardFrame (sp : ClassicalTimeSpace) : ClassicalTimeFrame sp :=
    PhysAffineFrame.Standard sp
def BuildClassicalTimeFrame {sp : ClassicalTimeSpace } : ClassicalTimeFrame sp → ClassicalTimeFrame sp
| (fr : ClassicalTimeFrame sp) := PhysAffineFrame.Derived sp fr
def BuildClassicalTimeVector {sp : ClassicalTimeSpace} (fr : PhysAffineFrame sp) (x : ℝ)
        : ClassicalTimeVector sp :=
    BuildAffinePhysVector1 fr x 
def BuildClassicalTimePoint {sp : ClassicalTimeSpace} (fr : PhysAffineFrame sp) (x : ℝ)
        : ClassicalTimePoint sp :=
    BuildAffinePhysPoint1 fr x 

def p := ([] : list ℕ)

def t : list ℕ := 1 :: [] 

abbreviation RealScalar := PhysScalar dimensionless
abbreviation EuclideanGeometryScalar := PhysScalar meters
abbreviation ClassicalTimeScalar := PhysScalar time
abbreviation ClassicalVelocityScalar := PhysScalar velocity
abbreviation EuclideanGeometry3Scalar := EuclideanGeometryScalar
abbreviation ClassicalVelocity3Scalar := ClassicalVelocityScalar


def RealScalarDefault : RealScalar := ⟨0⟩
def EuclideanGeometry3ScalarDefault (sp : EuclideanGeometrySpace 3) : EuclideanGeometryScalar := ⟨0⟩
def ClassicalTimeScalarDefault (sp : ClassicalTimeSpace ) : ClassicalTimeScalar := ⟨0⟩
def ClassicalVelocity3ScalarDefault (sp : ClassicalVelocitySpace 3)  : ClassicalVelocityScalar := ⟨0⟩


abbreviation NatDefault := (0 : ℕ)
abbreviation RationalDefault := (0 : ℚ)


def EuclideanGeometry3VectorDefault (sp : EuclideanGeometrySpace 3) {fr : EuclideanGeometryFrame sp} : EuclideanGeometryVector sp :=
    BuildEuclideanGeometry3Vector fr 0 0 0

def ClassicalVelocity3VectorDefault (sp : ClassicalVelocitySpace 3) : ClassicalVelocityVector sp :=
    BuildClassicalVelocity3Vector (PhysAffineSpace.GetStandardFrame sp) 0 0 0

def ClassicalTimeVectorDefault (sp : ClassicalTimeSpace ) : ClassicalTimeVector sp :=
    BuildClassicalTimeVector (PhysAffineSpace.GetStandardFrame sp) 0 


def EuclideanGeometry3PointDefault (sp : EuclideanGeometrySpace 3) : EuclideanGeometryPoint sp :=
    BuildEuclideanGeometry3Point (PhysAffineSpace.GetStandardFrame sp) 0 0 0
--abbreviation ClassicalVelocity3Point_zero := ClassicalVelocity3PointStruct.mk vel (aff_pt.mk [1,0,0,0] rfl rfl) std 
def ClassicalTimePointDefault (sp : ClassicalTimeSpace ) : ClassicalTimePoint sp :=
    BuildClassicalTimePoint (PhysAffineSpace.GetStandardFrame sp) 0 

