# Brief Notes

- I've left out affine combinations, mentioned specifically on 10/8. They introduce complexity in that we need a proof that the coefficients sum to 1, just like mass.
- I have largely omitted dimension conversions from Lang and Phys due to prior confusion and uncertainty as to how this will manifest
- We really should be able to handle angles and quaternions, especially if we're using ROS with a focus on transformations.
- I have omitted the following set of derived dimensions which I am not sure are of immediate interest/related to ROS, and only require length and time:
1. Area 
2. Volume
3. Radians
4. Steradians
5. Angular Velocity
6. Angular Acceleration

- Listing only tf constructs. Input API is not exhaustive and I think mostly tentative and demonstrative at this point.

- "->" is strictly functional notation, not a pointer symbol

# Peirce Input API

### tfScalarMatcher
```
+ -> tfScalar -> tfScalar -> REAL1_EXPR
- -> tfScalar -> tfScalar -> REAL1_EXPR
* -> tfScalar -> tfScalar -> REAL1_EXPR
/ -> tfScalar -> tfScalar -> REAL1_EXPR
tf::Vector3.angle() -> REAL1_EXPR
tf::Vector3.distance() -> REAL1_EXPR
tf::Vector3.distance2() -> REAL1_EXPR
tf::Vector3.dot() -> REAL1_EXPR
tf::Vector3.length() -> REAL1_EXPR
tf::Vector3.length2() -> REAL1_EXPR
tf::Vector3.x() -> REAL1_EXPR
tf::Vector3.y() -> REAL1_EXPR
tf::Vector3.z() -> REAL1_EXPR
tf::Vector3.getX() -> REAL1_EXPR
tf::Vector3.getY() -> REAL1_EXPR
tf::Vector3.getZ() -> REAL1_EXPR
```
### tf::Vector3
```
tf::Vector3.absolute() -> REAL3_EXPR
cross -> tf::Vector3 -> tf::Vector3 -> REAL3_EXPR
tf::Vector3.normalized() -> REAL3_EXPR
* -> tf::Vector3 -> tf::Vector3 -> REAL3_EXPR
* -> tf::Vector3 -> tfScalar -> REAL3_EXPR
/ -> tf::Vector3 -> tfScalar -> REAL3_EXPR
- -> tf::Vector3 -> tf::Vector3 -> REAL3_EXPR
+ -> tf::Vector3 -> tf::Vector3 -> REAL3_EXPR
* -> tf::Transform -> tf::Vector3 -> REAL3_EXPR
tf::Vector3() -> tfScalar -> tfScalar -> tfScalar -> REAL3_EXPR
```
### tf::Stamped<tf::Vector3> 

**Inherits tf::Vector3**


### tf::Matrix3x3

tf::Matrix3x3 -> tfScalar -> tfScalar -> tfScalar -> tfScalar -> tfScalar -> tfScalar -> tfScalar -> tfScalar -> tfScalar -> REALMATRIX3_EXPR
tf::Matrix3x3 -> tf::Matrix3x3 -> tf::Matrix3x3

### tf::Stamped<tf::Matrix3x3>

**Inherits tf::Matrix3x3**


### bool
```
&& -> int -> int -> BOOL_EXPR
|| -> int -> int -> BOOL_EXPR
== -> int -> int -> BOOL_EXPR
>= -> int -> int -> BOOL_EXPR
<= -> int -> int -> BOOL_EXPR
> -> int -> int -> BOOL_EXPR
< -> int -> int -> BOOL_EXPR
== -> tf::Vector3 -> tf::Vector3 -> BOOL_EXPR
>= -> tf::Vector3 -> tf::Vector3 -> BOOL_EXPR
<= -> tf::Vector3 -> tf::Vector3 -> BOOL_EXPR
> -> tf::Vector3 -> tf::Vector3 -> BOOL_EXPR
< -> tf::Vector3 -> tf::Vector3 -> BOOL_EXPR
== -> tfScalar -> tfScalar -> BOOL_EXPR
>= -> tfScalar -> tfScalar -> BOOL_EXPR
<= -> tfScalar -> tfScalar -> BOOL_EXPR
> -> tfScalar -> tfScalar -> BOOL_EXPR
< -> tfScalar -> tfScalar -> BOOL_EXPR
```
### tf::Quaternion
```
tf::Quaternion() -> tfScalar -> tfScalar -> tfScalar -> REAL4_EXPR
tf::Transform -> tf::Quaternion -> REAL4_EXPR
tf::Quaternion -> tf::Quaternion -> REAL4_EXPR
tf::Quaternion -> tf::Quaternion -> REAL4_EXPR
```
### tf::Transform
```
tf::Transform() -> tf::Quaternion -> tf::Vector3 -> REALMATRIX4_EXPR
tf::Transform() -> tf::Matrix3x3 -> tf::Vector3 -> REALMATRIX4_EXPR
* -> tf::Transform -> tf::Transform -> REALMATRIX4_EXPR
```
### tf::Pose

**Inherits tf::Transform**


# Peirce Interpretation API

### Spaces

**Euclidean Geometry Space**
```
Name: string,
Dimension: integer
```

**Classical Time Space**
```
Name: string
```

**Classical Velocity**
```
Name: string,
Space1: Euclidean Geometry Space,
Space2: ClassicalTime Space
```

**Classical Acceleration**
```
Name: string,
Space1: ClassicalVelocity Space,
Space2: ClassicalTime Space
```

### Vectors

**Euclidean Geometry Vector**
```
Name: string,
Space: Euclidean Geometry Space,
Value: float[Space.Dimension],
Frame: Euclidean Geometry Frame
```

**Classical Time Vector**
```
Name: string,
Space: Classical Time Space,
Value: float[1]
Frame: Classical Time Frame
```

**Classical Velocity Vector**
```
Name: string,
Space: Classical Velocity Space,
Value: float[Space.Dimension],
Frame: Classical Velocity Frame
```

**Classical Acceleration Vector**
```
Name: string,
Space: Classical Acceleration Space,
Value: float[Space.Dimension],
Frame: Classical Acceleration Frame
```

### Points

**Euclidean Geometry Point**
```
Name: string,
Space: Euclidean Geometry Space,
Value: float[Space.Dimension],
Frame: Euclidean Geometry Frame
```

**Classical Time Point**
```
Name: string,
Space: Classical Time Space,
Value: float,
Frame: Classical Time Frame
```

### Transformations

**Euclidean Geometry Transform**
```
Name: string,
Space: Euclidean Geometry Space,
Value: (float[Space.Dimension][Space.Dimension], float[Space.Dimension])
```

**Classical Time Transform**
```
Name: string,
Space: Classical Time Space,
Value: (float, float)
```

**Classical Velocity Transform**
```
Name: string,
Space: Classical Velocity Space,
Value: (float[Space.Dimension][Space.Dimension], float[Space.Dimension])
```

**Classical Acceleration Transform**
```
Name: string,
Space: Classical Acceleration Space,
Value: (float[Space.Dimension][Space.Dimension], float[Space.Dimension])
```

### Frames

**Euclidean Geometry Frame Alias**
```
Name: string,
Space: Euclidean Geometry Space,
Aliased: Euclidean Geometry Frame
```

**Euclidean Geometry Derived Frame**
```
Name: string,
Space: Classical Acceleration Space,
Value: (float[Space.Dimension][Space.Dimension], float[Space.Dimension]),
Parent: Euclidean Geometry Frame
```

**Classical Time Frame Alias**
```
Name: string,
Space: Classical Time Space,
Aliased: Classical Time Frame
```

**Classical Time Derived Frame**
```
Name: string,
Space: Classical Acceleration Space,
Value: (float[Space.Dimension][Space.Dimension], float[Space.Dimension]),
Parent: Classical Time Frame
```

**Classical Velocity Frame Alias**
```
Name: string,
Space: Classical Velocity Space,
Aliased: Classical Velocity Frame
```

**Classical Velocity Derived Frame**
```
Name: string,
Space: Classical Acceleration Space,
Value: (float[Space.Dimension][Space.Dimension], float[Space.Dimension]),
Parent: Classical Velocity Frame
```

**Classical Acceleration Frame Alias**
```
Name: string,
Space: Classical Acceleration Space,
Aliased: Classical Acceleration Frame
```

**Classical Acceleration Derived Frame**
```
Name: string,
Space: Classical Acceleration Space,
Value: (float[Space.Dimension][Space.Dimension], float[Space.Dimension]),
Parent: Classical Acceleration Frame
```

### Scalars

**Euclidean Geometry Scalar**
```
Name: string,
Space: Euclidean Geometry Space,
Value: float
```

**Classical Time Scalar**
```
Name: string,
Space: Classical Time Space,
Value: float
```

**Classical Velocity Scalar**
```
Name: string,
Space: Classical Velocity Space,
Value: float
```

**Classical Acceleration Scalar**
```
Name: string,
Space: Classical Acceleration Space,
Value: float
```

### Quantities

**Euclidean Geometry Quantity**
```
Name: string,
Space: Euclidean Geometry Space,
Value: float
```

**Classical Time Quantity**
```
Name: string,
Space: Classical Time Space,
Value: float
```

**Classical Velocity Quantity**
```
Name: string,
Space: Classical Velocity Space,
Value: float
```

**Classical Acceleration Quantity**
```
Name: string,
Space: Classical Acceleration Space,
Value: float
```

# Phys API

### Spaces

**euclideanGeometry**
```
id : nat,
dim: nat
```

**classicalTime**
```
id : nat
```

**classicalVelocity**
```
id : nat,
g: euclideanGeometry,
t: classicalTime
```

**classicalAcceleration**
```
id: nat,
v: classicalVelocity, 
t: classicalTime
```

### Vectors

**euclideanGeometryVector**
```
id: nat,
e : euclideanGeometry,
values : vector R e.dim,
m : MeasurementSystem
```

**classicalTimeVector**
```
id: nat,
t : classicalTime,
values : vector R 1,
m : MeasurementSystem
```

**classicalVelocityVector**
```
id: nat,
v : classicalVelocity,
values : vector R v.dim,
m : MeasurementSystem
```

**classicalAccelerationVector**
```
id: nat,
v : classicalAcceleration,
values : vector R v.dim,
m : MeasurementSystem
```

### Points

**euclideanGeometryPoint**
```
id: nat,
e : euclideanGeometry,
values : vector R v.dim,
m : MeasurementSystem
```

**classicalTimePoint**
```
id: nat,
t : classicalTime,
values : vector R v.dim,
m : MeasurementSystem
```

### Transformations

**euclideanGeometryTransform**
```
id: nat,
e : euclideanGeometry,
values: (nat -> vector R e.dim, vector R e.dim)
```

**classicalTimeTransform**
```
id: nat,
e : classicalTime,
values: (nat -> vector R e.dim, vector R e.dim)
```

**classicalVelocityTransform**
```
id: nat,
e : classicalVelocity,
values: (nat -> vector R e.dim, vector R e.dim)
```

**classicalAccelerationTransform**
```
id: nat,
e : classicalAcceleration,
values: (nat -> vector R e.dim, vector R e.dim)
```

### Frames

**euclideanGeometryDerivedFrame**
```
id: nat,
e : euclideanGeometry,
values: (nat -> vector R e.dim, vector R e.dim),
parent: euclideanGeometryFrame
```

**classicalTimeDerivedFrame**
```
id: nat,
e : classicalTime,
values: (nat -> vector R e.dim, vector R e.dim),
parent: classicalTimeFrame
```

**classicalVelocityDerivedFrame**
```
id: nat,
e : classicalVelocity,
values: (nat -> vector R e.dim, vector R e.dim),
parent: classicalVelocityFrame
```

**classicalAccelerationDerivedFrame**
```
id: nat,
e : classicalAcceleration,
values: (nat -> vector R e.dim, vector R e.dim),
parent: classicalAccelerationFrame
```

**getEuclideanGeometryStandardFrame**
```
e : euclideanGeometry
```

**getClassicalTimeStandardFrame**
```
e : classicalTime
```

**getClassicalVelocityStandardFrame**
```
e : classicalVelocity
```

**getClassicalAccelerationStandardFrame**
```
e : classicalAcceleration
```

### Scalars

**euclideanGeometryScalar**
```
id: nat,
e: euclideanGeometry,
values: R
```

**classicalTimeScalar**
```
id: nat,
e: euclideanGeometry,
values: R
```

**classicalVelocityScalar**
```
id: nat,
e: euclideanGeometry,
values: R
```

**classicalAccelerationScalar**
```
id: nat,
e: euclideanGeometry,
values: R
```

### Quantities

**euclideanGeometryQuantity**
```
id: nat,
e: euclideanGeometry,
values: R,
frame: euclideanGeometryFrame
```

**classicalTimeQuantity**
```
id: nat,
e: euclideanGeometry,
values: R,
frame: classicalTimeFrame
```

**classicalVelocityQuantity**
```
id: nat,
e: euclideanGeometry,
values: R,
frame: classicalVelocityFrame
```

**classicalAccelerationQuantity**
```
id: nat,
e: euclideanGeometry,
values: R,
frame: classicalAccelerationFrame
```



# Lang API

### Commands (cmd)

**seq**
```
cmd -> cmd -> cmd
```

**while**
```
bExpr -> cmd -> cmd
```

**if-then-else**
```
bExpr -> cmd -> cmd -> cmd
```

**euclideanGeometryAssmt**
```
euclideanGeometry.var -> euclideanGeometry.expr -> cmd
```

**euclideanGeometryVectorAssmt**
```
euclideanGeometry.vectorVar -> euclideanGeometry.vectorExpr -> cmd
```

**euclideanGeometryPointAssmt**
```
euclideanGeometry.pointVar -> euclideanGeometry.pointExpr -> cmd
```

**euclideanGeometryTransformationAssmt**
```
euclideanGeometry.transformationVar -> euclideanGeometry.transformationExpr -> cmd
```

**euclideanGeometryFrameAssmt**
```
euclideanGeometry.frameVar -> euclideanGeometry.frameExpr -> cmd
```

**euclideanGeometryScalarAssmt**
```
euclideanGeometry.scalarVar -> euclideanGeometry.scalarExpr -> cmd
```

**euclideanGeometryQuantityAssmt**
```
euclideanGeometry.quantityVar -> euclideanGeometry.quantityExpr -> cmd
```

**classicalTimeAssmt**
```
classicalTime.var -> classicalTime.expr -> cmd
```

**classicalTimeVectorAssmt**
```
classicalTime.vectorVar -> classicalTime.vectorExpr -> cmd
```

**classicalTimePointAssmt**
```
classicalTime.pointVar -> classicalTime.pointExpr -> cmd
```

**classicalTimeTransformationAssmt**
```
classicalTime.transformationVar -> classicalTime.transformationExpr -> cmd
```

**classicalTimeFrameAssmt**
```
classicalTime.frameVar -> classicalTime.frameExpr -> cmd
```

**classicalTimeScalarAssmt**
```
classicalTime.scalarVar -> classicalTime.scalarExpr -> cmd
```

**classicalTimeQuantityAssmt**
```
classicalTime.quantityVar -> classicalTime.quantityExpr -> cmd
```

**classicalVelocityAssmt**
```
classicalVelocity.var -> classicalTime.expr -> cmd
```

**classicalVelocityVectorAssmt**
```
classicalVelocity.vectorVar -> classicalVelocity.vectorExpr -> cmd
```

**classicalVelocityPointAssmt**
```
classicalVelocity.pointVar -> classicalVelocity.pointExpr -> cmd
```

**classicalVelocityTransformationAssmt**
```
classicalVelocity.transformationVar -> classicalVelocity.transformationExpr -> cmd
```

**classicalVelocityFrameAssmt**
```
classicalVelocity.frameVar -> classicalVelocity.frameExpr -> cmd
```

**classicalVelocityScalarAssmt**
```
classicalVelocity.scalarVar -> classicalVelocity.scalarExpr -> cmd
```

**classicalVelocityQuantityAssmt**
```
classicalVelocity.quantityVar -> classicalVelocity.quantityExpr -> cmd
```

**classicalAccelerationAssmt**
```
classicalAcceleration.var -> classicalAcceleration.expr -> cmd
```

**classicalAccelerationVectorAssmt**
```
classicalAcceleration.vectorVar -> classicalAcceleration.vectorExpr -> cmd
```

**classicalAccelerationTransformationAssmt**
```
classicalAcceleration.transformationVar -> classicalAcceleration.transformationExpr -> cmd
```

**classicalAccelerationFrameAssmt**
```
classicalAcceleration.frameVar -> classicalAcceleration.frameExpr -> cmd
```

**classicalAccelerationScalarAssmt**
```
classicalAcceleration.scalarVar -> classicalAcceleration.scalarExpr -> cmd
```

**classicalAccelerationQuantityAssmt**
```

classicalAcceleration.quantityVar -> classicalAcceleration.quantityExpr -> cmd
```


**classicalJerkAssmt**
```
classicalJerk.var -> classicalJerk.expr -> cmd
```

**classicalJerkVectorAssmt**
```
classicalJerk.vectorVar -> classicalJerk.vectorExpr -> cmd
```

**classicalJerkTransformationAssmt**
```
classicalJerk.transformationVar -> classicalJerk.transformationExpr -> cmd
```

**classicalJerkFrameAssmt**
```
classicalJerk.frameVar -> classicalJerk.frameExpr -> cmd
```

**classicalJerkScalarAssmt**
```
classicalJerk.scalarVar -> classicalJerk.scalarExpr -> cmd
```

**classicalJerkQuantityAssmt**
```
classicalJerk.quantityVar -> classicalJerk.quantityExpr -> cmd
```



### euclideanGeometry

**euclideanGeometry.var**
```
id : nat
```

**euclideanGeometry.expr**
```
1. lit :
e : euclideanGeometry
2. var :
v : euclideanGeometry.var

```

**euclideanGeometry.vectorVar**
```
id : nat
```

**euclideanGeometry.vectorExpr**
```

1. lit : 
euclideanGeometryVector
2. var : 
euclideanGeometry.vectorVar
```

**euclideanGeometry.pointVar**
```
id : nat
```

**euclideanGeometry.pointExpr**
```
1. lit :
euclideanGeometryPoint
2. var :
euclideanGeometry.pointVar
```

**euclideanGeometry.frameVar**
```
id : nat
```

**euclideanGeometry.frameExpr**
```
1. lit :
euclideanGeometryFrame
2. var :
euclideanGeometry.frameVar
```

**euclideanGeometry.transformationVar**
```
id : nat
```

**euclideanGeometry.transformationExpr**
```
1. lit :
euclideanGeometryTransformation
2. var :
euclideanGeometry.transformationVar
```

**euclideanGeometry.scalarVar**
```
id : nat
```

**euclideanGeometry.scalarExpr**
```
1. lit :
euclideanGeometryScalar
2. var :
euclideanGeometry.scalarVar
```

**euclideanGeometry.quantityVar**
```
id : nat
```

**euclideanGeometry.quantityExpr**
```
1. lit :
euclideanGeometryQuantity
2. var :
euclideanGeometry.quantityVar
```

### classicalTime


**classicalTime.var**
```
id : nat
```

**classicalTime.expr**
```
1. lit :
t : classicalTime
2. var :
v : classicalTime.var

```

**classicalTime.vectorVar**
```
id : nat
```

**classicalTime.vectorExpr**
```
1. lit : 
classicalTimeVector
2. var : 
classicalTime.vectorVar
```

**classicalTime.pointVar**
```
id : nat
```

**classicalTime.pointExpr**
```
1. lit :
classicalTimePoint
2. var :
classicalTime.pointVar
```

**classicalTime.frameVar**
```
id : nat
```

**classicalTime.frameExpr**
```
1. lit :
classicalTimeFrame
2. var :
classicalTime.frameVar
```

**classicalTime.transformationVar**
```
id : nat
```

**classicalTime.transformationExpr**
```
1. lit :
classicalTimeTransformation
2. var :
classicalTime.transformationVar
```

**classicalTime.scalarVar**
```
id : nat
```

**classicalTime.scalarExpr**
```
1. lit :
classicalTimeScalar
2. var :
classicalTime.scalarVar
```

**classicalTime.quantityVar**
```
id : nat
```

**classicalTime.quantityExpr**
```
1. lit :
classicalTimeQuantity
2. var :
classicalTime.quantityVar
```

### classicalVelocity


**classicalVelocity.var**
```
id : nat
```

**classicalVelocity.expr**
```
1. lit :
v : classicalVelocity
2. var :
v : classicalVelocity.var
3. div :
e : euclideanGeometry.expr, t : classicalTime.expr
```

**classicalVelocity.vectorVar**
```
id : nat
```

**classicalVelocity.vectorExpr**
```
1. lit : 
classicalVelocityVector
2. var : 
classicalVelocity.vectorVar
```

**classicalVelocity.frameVar**
```
id : nat
```

**classicalVelocity.frameExpr**
```
1. lit :
classicalVelocityFrame
2. var :
classicalVelocity.frameVar
```

**classicalVelocity.transformationVar**
```
id : nat
```

**classicalVelocity.transformationExpr**
```
1. lit :
classicalVelocityTransformation
2. var :
classicalVelocity.transformationVar
```

**classicalVelocity.scalarVar**
```
id : nat
```

**classicalVelocity.scalarExpr**
```
1. lit :
classicalVelocityScalar
2. var :
classicalVelocity.scalarVar
```

**classicalVelocity.quantityVar**
```
id : nat
```

**classicalVelocity.quantityExpr**
```
1. lit :
classicalVelocityQuantity
2. var :
classicalVelocity.quantityVar
```



### classicalAcceleration


**classicalAcceleration.var**
```
id : nat
```

**classicalAcceleration.expr**
```
1. lit :
a : classicalAcceleration
2. var :
v : classicalAcceleration.var
3. div :
v : classicalVelocity.expr, t : classicalTime.expr
```

**classicalAcceleration.vectorVar**
```
id : nat
```

**classicalAcceleration.vectorExpr**
```
1. lit : 
classicalAccelerationVector
2. var : 
classicalAcceleration.vectorVar
```

**classicalAcceleration.frameVar**
```

id : nat
```

**classicalAcceleration.frameExpr**
```
1. lit :
classicalAccelerationFrame
2. var :
classicalAcceleration.frameVar
```

**classicalAcceleration.transformationVar**
```
id : nat
```

**classicalAcceleration.transformationExpr**
```
1. lit :
classicalAccelerationTransformation
2. var :
classicalAcceleration.transformationVar
```

**classicalAcceleration.scalarVar**
```
id : nat
```

**classicalAcceleration.scalarExpr**
```

1. lit :
classicalAccelerationScalar
2. var :
classicalAcceleration.scalarVar
```

**classicalAcceleration.quantityVar**
```
id : nat
```

**classicalAcceleration.quantityExpr**
```
1. lit :
classicalAccelerationQuantity
2. var :
classicalAcceleration.quantityVar
```

### classicalJerk


**classicalJerk.var**
```
id : nat
```

**classicalJerk.expr**
```
1. lit :
a : classicalJerk
2. var :
v : classicalJerk.var
3. div :
v : classicalJerk.expr, t : classicalTime.expr
```

**classicalJerk.vectorVar**
```
id : nat
```

**classicalJerk.vectorExpr**
```
1. lit : 
classicalJerkVector
2. var : 
classicalJerk.vectorVar
```

**classicalJerk.frameVar**
```
id : nat
```

**classicalJerk.frameExpr**
```
1. lit :
classicalJerkFrame
2. var :
classicalJerk.frameVar
```

**classicalJerk.transformationVar**
```
id : nat
```

**classicalJerk.transformationExpr**
```
1. lit :
classicalJerkTransformation
2. var :
classicalJerk.transformationVar
```

**classicalJerk.scalarVar**
```
id : nat
```

**classicalJerk.scalarExpr**
```

1. lit :
classicalJerkScalar
2. var :
classicalJerk.scalarVar
```

**classicalJerk.quantityVar**
```

id : nat
```

**classicalJerk.quantityExpr**
```

1. lit :
classicalJerkQuantity
2. var :
classicalJerk.quantityVar
```

