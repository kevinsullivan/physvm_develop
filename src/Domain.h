
#ifndef BRIDGE_H
#define BRIDGE_H

#ifndef leanInferenceWildcard
#define leanInferenceWildcard "_"
#endif

#include <cstddef>  
#include "clang/AST/AST.h"
#include <vector>
#include <string>

#include "AST.h"
#include "Coords.h"

#include <g3log/g3log.hpp>


using namespace std;

/*
- Space
- Ident
- Expr
- Value
- Defn
*/

namespace domain{



class Space;
class MapSpace;
class DomainObject;
class DomainContainer;

class EuclideanGeometry;

class Geometric3Rotation;

class Geometric3Orientation;

class Geometric3Angle;

class Geometric3FrameChange;

class Geometric3Point;

class Geometric3HomogenousPoint;

class Geometric3Vector;

class Geometric3Scalar;

class Geometric3BasisChange;

class Geometric3Scaling;

class Geometric3Shear;

class ClassicalTime;

class TimeFrameChange;

class TimePoint;

class TimeHomogenousPoint;

class TimeVector;

class TimeScalar;

class TimeBasisChange;

class TimeScaling;

class TimeShear;

class ClassicalVelocity;

class Velocity3Vector;

class Velocity3Scalar;

class Velocity3BasisChange;

class Velocity3Scaling;

class Velocity3Shear;

            
// Definition for Domain class 

class Domain {
public:
// Space
	std::vector<Space*>& getSpaces();


    Space* getSpace(std::string key);

    DomainObject* mkDefaultDomainContainer();
    DomainObject* mkDefaultDomainContainer(std::initializer_list<DomainObject*> operands);
    DomainObject* mkDefaultDomainContainer(std::vector<DomainObject*> operands);

	EuclideanGeometry* mkEuclideanGeometry(std::string key ,std::string name_, int dimension_);
	std::vector<EuclideanGeometry*> &getEuclideanGeometrySpaces() { return EuclideanGeometry_vec; }

	Geometric3Rotation* mkGeometric3Rotation(EuclideanGeometry* sp);
	Geometric3Rotation* mkGeometric3Rotation();
	std::vector<Geometric3Rotation*> &getGeometric3Rotations() { return Geometric3Rotation_vec; }

	Geometric3Orientation* mkGeometric3Orientation(EuclideanGeometry* sp);
	Geometric3Orientation* mkGeometric3Orientation();
	std::vector<Geometric3Orientation*> &getGeometric3Orientations() { return Geometric3Orientation_vec; }

	Geometric3Angle* mkGeometric3Angle(EuclideanGeometry* sp);
	Geometric3Angle* mkGeometric3Angle();
	std::vector<Geometric3Angle*> &getGeometric3Angles() { return Geometric3Angle_vec; }

	Geometric3FrameChange* mkGeometric3FrameChange(EuclideanGeometry* sp);
	Geometric3FrameChange* mkGeometric3FrameChange();
	std::vector<Geometric3FrameChange*> &getGeometric3FrameChanges() { return Geometric3FrameChange_vec; }

	Geometric3Point* mkGeometric3Point(EuclideanGeometry* sp);
	Geometric3Point* mkGeometric3Point();
	std::vector<Geometric3Point*> &getGeometric3Points() { return Geometric3Point_vec; }

	Geometric3HomogenousPoint* mkGeometric3HomogenousPoint(EuclideanGeometry* sp);
	Geometric3HomogenousPoint* mkGeometric3HomogenousPoint();
	std::vector<Geometric3HomogenousPoint*> &getGeometric3HomogenousPoints() { return Geometric3HomogenousPoint_vec; }

	Geometric3Vector* mkGeometric3Vector(EuclideanGeometry* sp);
	Geometric3Vector* mkGeometric3Vector();
	std::vector<Geometric3Vector*> &getGeometric3Vectors() { return Geometric3Vector_vec; }

	Geometric3Scalar* mkGeometric3Scalar(EuclideanGeometry* sp);
	Geometric3Scalar* mkGeometric3Scalar();
	std::vector<Geometric3Scalar*> &getGeometric3Scalars() { return Geometric3Scalar_vec; }

	Geometric3BasisChange* mkGeometric3BasisChange(EuclideanGeometry* sp);
	Geometric3BasisChange* mkGeometric3BasisChange();
	std::vector<Geometric3BasisChange*> &getGeometric3BasisChanges() { return Geometric3BasisChange_vec; }

	Geometric3Scaling* mkGeometric3Scaling(EuclideanGeometry* sp);
	Geometric3Scaling* mkGeometric3Scaling();
	std::vector<Geometric3Scaling*> &getGeometric3Scalings() { return Geometric3Scaling_vec; }

	Geometric3Shear* mkGeometric3Shear(EuclideanGeometry* sp);
	Geometric3Shear* mkGeometric3Shear();
	std::vector<Geometric3Shear*> &getGeometric3Shears() { return Geometric3Shear_vec; }

	ClassicalTime* mkClassicalTime(std::string key ,std::string name_);
	std::vector<ClassicalTime*> &getClassicalTimeSpaces() { return ClassicalTime_vec; }

	TimeFrameChange* mkTimeFrameChange(ClassicalTime* sp);
	TimeFrameChange* mkTimeFrameChange();
	std::vector<TimeFrameChange*> &getTimeFrameChanges() { return TimeFrameChange_vec; }

	TimePoint* mkTimePoint(ClassicalTime* sp);
	TimePoint* mkTimePoint();
	std::vector<TimePoint*> &getTimePoints() { return TimePoint_vec; }

	TimeHomogenousPoint* mkTimeHomogenousPoint(ClassicalTime* sp);
	TimeHomogenousPoint* mkTimeHomogenousPoint();
	std::vector<TimeHomogenousPoint*> &getTimeHomogenousPoints() { return TimeHomogenousPoint_vec; }

	TimeVector* mkTimeVector(ClassicalTime* sp);
	TimeVector* mkTimeVector();
	std::vector<TimeVector*> &getTimeVectors() { return TimeVector_vec; }

	TimeScalar* mkTimeScalar(ClassicalTime* sp);
	TimeScalar* mkTimeScalar();
	std::vector<TimeScalar*> &getTimeScalars() { return TimeScalar_vec; }

	TimeBasisChange* mkTimeBasisChange(ClassicalTime* sp);
	TimeBasisChange* mkTimeBasisChange();
	std::vector<TimeBasisChange*> &getTimeBasisChanges() { return TimeBasisChange_vec; }

	TimeScaling* mkTimeScaling(ClassicalTime* sp);
	TimeScaling* mkTimeScaling();
	std::vector<TimeScaling*> &getTimeScalings() { return TimeScaling_vec; }

	TimeShear* mkTimeShear(ClassicalTime* sp);
	TimeShear* mkTimeShear();
	std::vector<TimeShear*> &getTimeShears() { return TimeShear_vec; }

	ClassicalVelocity* mkClassicalVelocity(std::string key ,std::string name_, int dimension_);
	std::vector<ClassicalVelocity*> &getClassicalVelocitySpaces() { return ClassicalVelocity_vec; }

	Velocity3Vector* mkVelocity3Vector(ClassicalVelocity* sp);
	Velocity3Vector* mkVelocity3Vector();
	std::vector<Velocity3Vector*> &getVelocity3Vectors() { return Velocity3Vector_vec; }

	Velocity3Scalar* mkVelocity3Scalar(ClassicalVelocity* sp);
	Velocity3Scalar* mkVelocity3Scalar();
	std::vector<Velocity3Scalar*> &getVelocity3Scalars() { return Velocity3Scalar_vec; }

	Velocity3BasisChange* mkVelocity3BasisChange(ClassicalVelocity* sp);
	Velocity3BasisChange* mkVelocity3BasisChange();
	std::vector<Velocity3BasisChange*> &getVelocity3BasisChanges() { return Velocity3BasisChange_vec; }

	Velocity3Scaling* mkVelocity3Scaling(ClassicalVelocity* sp);
	Velocity3Scaling* mkVelocity3Scaling();
	std::vector<Velocity3Scaling*> &getVelocity3Scalings() { return Velocity3Scaling_vec; }

	Velocity3Shear* mkVelocity3Shear(ClassicalVelocity* sp);
	Velocity3Shear* mkVelocity3Shear();
	std::vector<Velocity3Shear*> &getVelocity3Shears() { return Velocity3Shear_vec; }

private:

	std::unordered_map<std::string, Space*> Space_map;
	std::vector<Space*> Space_vec;
	std::vector<EuclideanGeometry*> EuclideanGeometry_vec;
	std::vector<Geometric3Rotation*>Geometric3Rotation_vec;
	std::vector<Geometric3Orientation*>Geometric3Orientation_vec;
	std::vector<Geometric3Angle*>Geometric3Angle_vec;
	std::vector<Geometric3FrameChange*>Geometric3FrameChange_vec;
	std::vector<Geometric3Point*>Geometric3Point_vec;
	std::vector<Geometric3HomogenousPoint*>Geometric3HomogenousPoint_vec;
	std::vector<Geometric3Vector*>Geometric3Vector_vec;
	std::vector<Geometric3Scalar*>Geometric3Scalar_vec;
	std::vector<Geometric3BasisChange*>Geometric3BasisChange_vec;
	std::vector<Geometric3Scaling*>Geometric3Scaling_vec;
	std::vector<Geometric3Shear*>Geometric3Shear_vec;
	std::vector<ClassicalTime*> ClassicalTime_vec;
	std::vector<TimeFrameChange*>TimeFrameChange_vec;
	std::vector<TimePoint*>TimePoint_vec;
	std::vector<TimeHomogenousPoint*>TimeHomogenousPoint_vec;
	std::vector<TimeVector*>TimeVector_vec;
	std::vector<TimeScalar*>TimeScalar_vec;
	std::vector<TimeBasisChange*>TimeBasisChange_vec;
	std::vector<TimeScaling*>TimeScaling_vec;
	std::vector<TimeShear*>TimeShear_vec;
	std::vector<ClassicalVelocity*> ClassicalVelocity_vec;
	std::vector<Velocity3Vector*>Velocity3Vector_vec;
	std::vector<Velocity3Scalar*>Velocity3Scalar_vec;
	std::vector<Velocity3BasisChange*>Velocity3BasisChange_vec;
	std::vector<Velocity3Scaling*>Velocity3Scaling_vec;
	std::vector<Velocity3Shear*>Velocity3Shear_vec;
};


class Space {
public:
	Space() {};
    virtual ~Space(){};
	std::string toString() const {
		return "This is a mixin interface"; 
	}

private:
};


class MapSpace : public Space {
public:
	MapSpace() {}
	MapSpace(domain::Space domain, domain::Space codomain) : domain_{domain}, codomain_{codomain} {}

	std::string toString() const {
		return domain_.toString() + "->" + codomain_.toString(); 
	}
	domain::Space domain_;
	domain::Space codomain_;
};
class DomainObject {
public:
    DomainObject(std::initializer_list<DomainObject*> args);
    DomainObject(std::vector<DomainObject*> operands) : operands_(operands) {};
    DomainObject(){};
    DomainObject* getOperand(int i);
    std::vector<DomainObject*> getOperands() const { return operands_; };
    void setOperands(std::vector<DomainObject*> operands);
    virtual std::string toString();
    friend class DomainObject; 
  
protected:
    std::vector<DomainObject*> operands_;
    int operand_count;
};

class DomainContainer : public DomainObject{
public:
        DomainContainer() : DomainObject(), inner_(nullptr) {};
        DomainContainer(DomainObject* inner) : inner_(inner) {};
        DomainContainer(std::initializer_list<DomainObject*> operands);
        DomainContainer(std::vector<DomainObject*> operands);
        virtual std::string toString() override;// { this->hasValue() ? this->inner_->toString() : "No Provided Interpretation"; }
        DomainObject* getValue() const { return this->inner_; }
        void setValue(DomainObject* obj);
        bool hasValue();
        

private:
DomainObject* inner_;
};


class EuclideanGeometry : public Space {
public:
	EuclideanGeometry() : name_("") {};
	EuclideanGeometry(std::string name) : name_(name) {};
	EuclideanGeometry(std::string name, int dimension) : name_(name), dimension_(dimension) {};
	std::string getName() const { return name_; }; 
	int getDimension() const { return dimension_; }; 
	std::string toString() const {
		return "@@EuclideanGeometry " + getName()   + "("+ std::to_string(getDimension()) + ")"; 
	}

private:
    std::string name_;
    int dimension_;
};

class Geometric3Rotation : public DomainObject {
public:
    Geometric3Rotation(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    Geometric3Rotation(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~Geometric3Rotation(){}
    std::string toString() override {
        return "@@Geometric3Rotation(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    EuclideanGeometry* space_;
};


class Geometric3Orientation : public DomainObject {
public:
    Geometric3Orientation(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    Geometric3Orientation(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~Geometric3Orientation(){}
    std::string toString() override {
        return "@@Geometric3Orientation(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    EuclideanGeometry* space_;
};


class Geometric3Angle : public DomainObject {
public:
    Geometric3Angle(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    Geometric3Angle(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~Geometric3Angle(){}
    std::string toString() override {
        return "@@Geometric3Angle(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    EuclideanGeometry* space_;
};


class Geometric3FrameChange : public DomainObject {
public:
    Geometric3FrameChange(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    Geometric3FrameChange(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~Geometric3FrameChange(){}
    std::string toString() override {
        return "@@Geometric3FrameChange(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    EuclideanGeometry* space_;
};


class Geometric3Point : public DomainObject {
public:
    Geometric3Point(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    Geometric3Point(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~Geometric3Point(){}
    std::string toString() override {
        return "@@Geometric3Point(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    EuclideanGeometry* space_;
};


class Geometric3HomogenousPoint : public DomainObject {
public:
    Geometric3HomogenousPoint(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    Geometric3HomogenousPoint(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~Geometric3HomogenousPoint(){}
    std::string toString() override {
        return "@@Geometric3HomogenousPoint(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    EuclideanGeometry* space_;
};


class Geometric3Vector : public DomainObject {
public:
    Geometric3Vector(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    Geometric3Vector(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~Geometric3Vector(){}
    std::string toString() override {
        return "@@Geometric3Vector(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    EuclideanGeometry* space_;
};


class Geometric3Scalar : public DomainObject {
public:
    Geometric3Scalar(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    Geometric3Scalar(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~Geometric3Scalar(){}
    std::string toString() override {
        return "@@Geometric3Scalar(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    EuclideanGeometry* space_;
};


class Geometric3BasisChange : public DomainObject {
public:
    Geometric3BasisChange(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    Geometric3BasisChange(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~Geometric3BasisChange(){}
    std::string toString() override {
        return "@@Geometric3BasisChange(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    EuclideanGeometry* space_;
};


class Geometric3Scaling : public DomainObject {
public:
    Geometric3Scaling(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    Geometric3Scaling(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~Geometric3Scaling(){}
    std::string toString() override {
        return "@@Geometric3Scaling(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    EuclideanGeometry* space_;
};


class Geometric3Shear : public DomainObject {
public:
    Geometric3Shear(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    Geometric3Shear(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~Geometric3Shear(){}
    std::string toString() override {
        return "@@Geometric3Shear(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    EuclideanGeometry* space_;
};


class ClassicalTime : public Space {
public:
	ClassicalTime() : name_("") {};
	ClassicalTime(std::string name) : name_(name) {};
	
	std::string getName() const { return name_; }; 
	
	std::string toString() const {
		return "@@ClassicalTime " + getName()   + "(" + ")"; 
	}

private:
    std::string name_;
    
};

class TimeFrameChange : public DomainObject {
public:
    TimeFrameChange(ClassicalTime* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    TimeFrameChange(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~TimeFrameChange(){}
    std::string toString() override {
        return "@@TimeFrameChange(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    ClassicalTime* space_;
};


class TimePoint : public DomainObject {
public:
    TimePoint(ClassicalTime* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    TimePoint(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~TimePoint(){}
    std::string toString() override {
        return "@@TimePoint(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    ClassicalTime* space_;
};


class TimeHomogenousPoint : public DomainObject {
public:
    TimeHomogenousPoint(ClassicalTime* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    TimeHomogenousPoint(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~TimeHomogenousPoint(){}
    std::string toString() override {
        return "@@TimeHomogenousPoint(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    ClassicalTime* space_;
};


class TimeVector : public DomainObject {
public:
    TimeVector(ClassicalTime* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    TimeVector(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~TimeVector(){}
    std::string toString() override {
        return "@@TimeVector(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    ClassicalTime* space_;
};


class TimeScalar : public DomainObject {
public:
    TimeScalar(ClassicalTime* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    TimeScalar(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~TimeScalar(){}
    std::string toString() override {
        return "@@TimeScalar(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    ClassicalTime* space_;
};


class TimeBasisChange : public DomainObject {
public:
    TimeBasisChange(ClassicalTime* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    TimeBasisChange(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~TimeBasisChange(){}
    std::string toString() override {
        return "@@TimeBasisChange(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    ClassicalTime* space_;
};


class TimeScaling : public DomainObject {
public:
    TimeScaling(ClassicalTime* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    TimeScaling(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~TimeScaling(){}
    std::string toString() override {
        return "@@TimeScaling(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    ClassicalTime* space_;
};


class TimeShear : public DomainObject {
public:
    TimeShear(ClassicalTime* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    TimeShear(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~TimeShear(){}
    std::string toString() override {
        return "@@TimeShear(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    ClassicalTime* space_;
};


class ClassicalVelocity : public Space {
public:
	ClassicalVelocity() : name_("") {};
	ClassicalVelocity(std::string name) : name_(name) {};
	ClassicalVelocity(std::string name, int dimension) : name_(name), dimension_(dimension) {};
	std::string getName() const { return name_; }; 
	int getDimension() const { return dimension_; }; 
	std::string toString() const {
		return "@@ClassicalVelocity " + getName()   + "("+ std::to_string(getDimension()) + ")"; 
	}

private:
    std::string name_;
    int dimension_;
};

class Velocity3Vector : public DomainObject {
public:
    Velocity3Vector(ClassicalVelocity* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    Velocity3Vector(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~Velocity3Vector(){}
    std::string toString() override {
        return "@@Velocity3Vector(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    ClassicalVelocity* space_;
};


class Velocity3Scalar : public DomainObject {
public:
    Velocity3Scalar(ClassicalVelocity* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    Velocity3Scalar(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~Velocity3Scalar(){}
    std::string toString() override {
        return "@@Velocity3Scalar(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    ClassicalVelocity* space_;
};


class Velocity3BasisChange : public DomainObject {
public:
    Velocity3BasisChange(ClassicalVelocity* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    Velocity3BasisChange(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~Velocity3BasisChange(){}
    std::string toString() override {
        return "@@Velocity3BasisChange(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    ClassicalVelocity* space_;
};


class Velocity3Scaling : public DomainObject {
public:
    Velocity3Scaling(ClassicalVelocity* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    Velocity3Scaling(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~Velocity3Scaling(){}
    std::string toString() override {
        return "@@Velocity3Scaling(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    ClassicalVelocity* space_;
};


class Velocity3Shear : public DomainObject {
public:
    Velocity3Shear(ClassicalVelocity* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    Velocity3Shear(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~Velocity3Shear(){}
    std::string toString() override {
        return "@@Velocity3Shear(" + (space_?space_->getName():"Missing Space") + ")";
    }
private:
    ClassicalVelocity* space_;
};

} // end namespace

#endif