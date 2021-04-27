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


def env370 := environment.init_env

--

def time : classicalTime := classicalTime.build 10
def si : measurementSystem.MeasurementSystem := measurementSystem.si_measurement_system
def si_nano : measurementSystem.MeasurementSystem := measurementSystem.si_nanoseconds

def secs : classicalTimeQuantity time si := classicalTimeQuantity.build time si ⟨[5],rfl⟩
def nanos : classicalTimeQuantity time si_nano := classicalTimeQuantity.build time si_nano ⟨[6],rfl⟩

def fivesecs : classicalTimeQuantity time si := secs
def sixsecs : classicalTimeQuantity time si := nanos -- type error

--partially embedded

--def t : lang.classicalTime.spaceVar := ⟨⟨time⟩⟩ 
def v1 : lang.classicalTime.QuantityVar ⟨time, si⟩ := ⟨⟨6⟩⟩
--def v2 : lang.classicalTime.QuantityVar ⟨time, si⟩ 
def asn_okay : cmd 
	:= cmd.classicalTimeQuantityAssmt ⟨time, si⟩ v1 (lang.classicalTime.QuantityExpr.lit q1)

def asn_bad : cmd 
	:= cmd.classicalTimeQuantityAssmt ⟨time, si⟩ v1 (lang.classicalTime.QuantityExpr.lit q2)

--deply embedded 

def worldGeom := 
	let var := (⟨⟨8⟩⟩ : lang.euclideanGeometry.spaceVar 3) in
	let spaceLiteral := lang.euclideanGeometry.spaceExpr.lit(euclideanGeometry.build 3 1) in
	cmd.euclideanGeometryAssmt 3 var spaceLiteral
def env371 := cmdEval worldGeom env370


def worldTime := 
	let var := (⟨⟨10⟩⟩ : lang.classicalTime.spaceVar) in
	let spaceLiteral := lang.classicalTime.spaceExpr.lit(classicalTime.build 2) in
	cmd.classicalTimeAssmt var spaceLiteral
def env372 := cmdEval worldTime env371

def si := 	let var := (⟨⟨12⟩⟩ : lang.measurementSystem.measureVar) in
	let measurementSystemLiteral := (lang.measurementSystem.measureExpr.lit measurementSystem.si_measurement_system) in
	var=measurementSystemLiteral
def env373 := cmdEval si env372


def si_nanoseconds := 	let var := (⟨⟨16⟩⟩ : lang.measurementSystem.measureVar) in
	let measurementSystemLiteral := (lang.measurementSystem.measureExpr.lit measurementSystem.si_nanoseconds) in
	var=measurementSystemLiteral
def env373_2 := cmdEval si_nanoseconds env373

def nwu := 
	let var := (⟨⟨14⟩⟩ : lang.axisOrientation.orientationVar) in
	let axisOrientationLiteral := (lang.axisOrientation.orientationExpr.lit orientation.NWU) in
	var=axisOrientationLiteral
def env374 := cmdEval nwu env373


def secq :=
	let sp := (classicalTimeEval (lang.classicalTime.spaceExpr.var (⟨⟨10⟩⟩ : lang.classicalTime.spaceVar)) env374) in
	let ms := (measurementSystemEval (lang.measurementSystem.measureExpr.var ⟨⟨12⟩⟩) env374) in
	--let si := (measurementSystemEval (lang.measurementSystem.measureExpr.var ⟨⟨12⟩⟩) env374)
	--let var := (classicalTimeQuantiyEval (lang.classicalTime.QuantityExpr.var ⟨⟨12⟩⟩) env374) in
--	let qt : Σs : classicalTime, measurementSystem.MeasurementSystem := ⟨sp, ms⟩ in
	let var : lang.classicalTime.QuantityVar ⟨sp, ms⟩ := ⟨⟨20⟩⟩ in
	let literal : lang.classicalTime.QuantityExpr ⟨sp, ms⟩ := 
		(lang.classicalTime.QuantityExpr.lit (classicalTimeQuantity.build sp ms ⟨[1],rfl⟩ : classicalTimeQuantity sp ms) : lang.classicalTime.QuantityExpr ⟨sp, ms⟩) in
	cmd.classicalTimeQuantityAssmt ⟨sp, ms⟩ var literal
	

def env375 := cmdEval secq env374

def nanoq :=
	let sp := (classicalTimeEval (lang.classicalTime.spaceExpr.var ⟨⟨10⟩⟩) env375) in
	let ms := (measurementSystemEval (lang.measurementSystem.measureExpr.var ⟨⟨12⟩⟩) env375) in
	--let si := (measurementSystemEval (lang.measurementSystem.measureExpr.var ⟨⟨12⟩⟩) env374)
	--let var := (classicalTimeQuantiyEval (lang.classicalTime.QuantityExpr.var ⟨⟨12⟩⟩) env374) in
--	let qt : Σs : classicalTime, measurementSystem.MeasurementSystem := ⟨sp, ms⟩ in
	let var : lang.classicalTime.QuantityVar ⟨sp, ms⟩ := ⟨⟨22⟩⟩ in
	let literal : lang.classicalTime.QuantityExpr ⟨sp, ms⟩ := 
		(
		let sp1 := (classicalTimeEval (lang.classicalTime.spaceExpr.var ⟨⟨10⟩⟩) env375) in
		let ms1 := (measurementSystemEval (lang.measurementSystem.measureExpr.var ⟨⟨12⟩⟩) env375) in
		let lit := classicalTimeQuantityEval ⟨sp, ms⟩ (lang.classicalTime.QuantityExpr.lit (classicalTimeQuantity.build sp ms ⟨[1],rfl⟩ : classicalTimeQuantity sp ms) : lang.classicalTime.QuantityExpr ⟨sp, ms⟩) env375 in
		lang.classicalTime.QuantityExpr.lit lit		
		
		--classicalTimeQuantityEval ⟨sp, ms⟩ (lang.classicalTime.QuantityExpr.var (⟨⟨20⟩⟩ : lang.classicalTime.QuantityVar ⟨sp, ms⟩ )) env375
		) in
	cmd.classicalTimeQuantityAssmt ⟨sp, ms⟩ var literal

def env376 := cmdEval nanoq env375

--type errors are not clear based upon changing multiple parameters
--possibly due to eval "noncomputable"
def nanoq2 :=
	let sp := (classicalTimeEval (lang.classicalTime.spaceExpr.var ⟨⟨10⟩⟩) env376) in
	let ms := (measurementSystemEval (lang.measurementSystem.measureExpr.var ⟨⟨16⟩⟩) env376) in
	--let si := (measurementSystemEval (lang.measurementSystem.measureExpr.var ⟨⟨12⟩⟩) env374)
	--let var := (classicalTimeQuantiyEval (lang.classicalTime.QuantityExpr.var ⟨⟨12⟩⟩) env374) in
--	let qt : Σs : classicalTime, measurementSystem.MeasurementSystem := ⟨sp, ms⟩ in
	let var : lang.classicalTime.QuantityVar ⟨sp, ms⟩ := ⟨⟨22⟩⟩ in
	let sp1 := (classicalTimeEval (lang.classicalTime.spaceExpr.var ⟨⟨10⟩⟩) env376) in
	let ms1 := (measurementSystemEval (lang.measurementSystem.measureExpr.var ⟨⟨22⟩⟩) env376) in
	let literal : lang.classicalTime.QuantityExpr ⟨sp1,ms1⟩ := 
		(
		let lit := classicalTimeQuantityEval ⟨sp1, ms1⟩ (lang.classicalTime.QuantityExpr.var (⟨⟨20⟩⟩ : lang.classicalTime.QuantityVar ⟨sp1, ms1⟩ )) env376 in--classicalTimeQuantityEval ⟨sp, ms⟩ (lang.classicalTime.QuantityExpr.lit (classicalTimeQuantity.build sp ms ⟨[1],rfl⟩ : classicalTimeQuantity sp ms) : lang.classicalTime.QuantityExpr ⟨sp, ms⟩) env375 in
		lang.classicalTime.QuantityExpr.lit lit	
		
		--classicalTimeQuantityEval ⟨sp, ms⟩ (lang.classicalTime.QuantityExpr.var (⟨⟨20⟩⟩ : lang.classicalTime.QuantityVar ⟨sp, ms⟩ )) env375
		) in
		cmd.classicalTimeQuantityAssmt ⟨sp, ms⟩ var literal

	def env377 := cmdEval nanoq2 env376