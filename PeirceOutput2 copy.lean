import .lang.imperative_DSL.physlang

noncomputable theory

--errors not showing at line 100

/-
EXAMPLE 2 : UNITS MISMATCH

-/

/-
    float secs = 5;
    float nanos = 6;
    float fivesecs = secs;
    float sixsecs = nanos;
-/
open orientation


def env370 := environment.init_env

--

def WorldGeometry : euclideanGeometry 3 := euclideanGeometry.build 3 777
def si : measurementSystem.MeasurementSystem := measurementSystem.si_measurement_system
def enu : AxisOrientation 3 := ENU
def WorldFrame : euclideanGeometryFrame WorldGeometry := WorldGeometry.stdFrame
def LeftLegFrame : euclideanGeometryFrame WorldGeometry := 
	euclideanGeometryFrame.build_derived_from_coords 
		WorldFrame 
			⟨[1,1,1],rfl⟩ 
			⟨[
				⟨[0,1,0],rfl⟩,
				⟨[0,1,0],rfl⟩,
				⟨[0,1,0],rfl⟩],rfl
			⟩ 
		si enu
def RightLegFrame : euclideanGeometryFrame WorldGeometry := 
	euclideanGeometryFrame.build_derived_from_coords 
		WorldFrame 
			⟨[2,2,2],rfl⟩ 
			⟨[
				⟨[1,0,0],rfl⟩,
				⟨[0,0,1],rfl⟩,
				⟨[0,1,0],rfl⟩],rfl
			⟩ 
		si enu


def LeftToWorld : euclideanGeometryTransform LeftLegFrame WorldFrame := 
	euclideanGeometryTransform.build _ _
def RightVec : euclideanGeometryCoordinateVector RightLegFrame := 
	euclideanGeometryCoordinateVector.build RightLegFrame ⟨[0,0,0],rfl⟩ 
def ApplyResult : euclideanGeometryCoordinateVector WorldFrame :=
	geom_trans_apply_vec LeftToWorld RightVec