
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
class Frame;
class DomainObject;
class DomainContainer;

class EuclideanGeometry;

class EuclideanGeometry3Frame;

class EuclideanGeometry3Rotation;

class EuclideanGeometry3Orientation;

class EuclideanGeometry3Angle;

class EuclideanGeometry3FrameChange;

class EuclideanGeometry3Point;

class EuclideanGeometry3HomogenousPoint;

class EuclideanGeometry3Vector;

class EuclideanGeometry3Scalar;

class EuclideanGeometry3BasisChange;

class EuclideanGeometry3Scaling;

class EuclideanGeometry3Shear;

class ClassicalTime;

class ClassicalTimeFrame;

class ClassicalTimeFrameChange;

class ClassicalTimePoint;

class ClassicalTimeHomogenousPoint;

class ClassicalTimeVector;

class ClassicalTimeScalar;

class ClassicalTimeBasisChange;

class ClassicalTimeScaling;

class ClassicalTimeShear;

class ClassicalVelocity;

class ClassicalVelocity3Frame;

class ClassicalVelocity3Vector;

class ClassicalVelocity3Scalar;

class ClassicalVelocity3BasisChange;

class ClassicalVelocity3Scaling;

class ClassicalVelocity3Shear;

            
// Definition for Domain class 

class Domain {
public:
// Space
	std::vector<Space*>& getSpaces();


    Space* getSpace(std::string key);

    DomainObject* mkDefaultDomainContainer();
    DomainObject* mkDefaultDomainContainer(std::initializer_list<DomainObject*> operands);
    DomainObject* mkDefaultDomainContainer(std::vector<DomainObject*> operands);
    Frame* mkFrame(std::string name, Space* space, Frame* parent);


    MapSpace* mkMapSpace(Space* space, Frame* dom, Frame* cod);

	EuclideanGeometry* mkEuclideanGeometry(std::string key ,std::string name_, int dimension_);
	std::vector<EuclideanGeometry*> &getEuclideanGeometrySpaces() { return EuclideanGeometry_vec; }

	EuclideanGeometry3Frame* mkEuclideanGeometry3Frame(std::string name, domain::EuclideanGeometry* space, domain::EuclideanGeometry3Frame* parent);
	EuclideanGeometry3Rotation * mkEuclideanGeometry3Rotation(EuclideanGeometry* sp);
	EuclideanGeometry3Rotation* mkEuclideanGeometry3Rotation();
	std::vector<EuclideanGeometry3Rotation*> &getEuclideanGeometry3Rotations() { return EuclideanGeometry3Rotation_vec; }

	EuclideanGeometry3Orientation * mkEuclideanGeometry3Orientation(EuclideanGeometry* sp);
	EuclideanGeometry3Orientation* mkEuclideanGeometry3Orientation();
	std::vector<EuclideanGeometry3Orientation*> &getEuclideanGeometry3Orientations() { return EuclideanGeometry3Orientation_vec; }

	EuclideanGeometry3Angle * mkEuclideanGeometry3Angle(EuclideanGeometry* sp);
	EuclideanGeometry3Angle* mkEuclideanGeometry3Angle();
	std::vector<EuclideanGeometry3Angle*> &getEuclideanGeometry3Angles() { return EuclideanGeometry3Angle_vec; }

	EuclideanGeometry3FrameChange * mkEuclideanGeometry3FrameChange(MapSpace* sp);
	EuclideanGeometry3FrameChange* mkEuclideanGeometry3FrameChange();
	std::vector<EuclideanGeometry3FrameChange*> &getEuclideanGeometry3FrameChanges() { return EuclideanGeometry3FrameChange_vec; }

	EuclideanGeometry3Point * mkEuclideanGeometry3Point(EuclideanGeometry* sp);
	EuclideanGeometry3Point* mkEuclideanGeometry3Point();
	std::vector<EuclideanGeometry3Point*> &getEuclideanGeometry3Points() { return EuclideanGeometry3Point_vec; }

	EuclideanGeometry3HomogenousPoint * mkEuclideanGeometry3HomogenousPoint(EuclideanGeometry* sp);
	EuclideanGeometry3HomogenousPoint* mkEuclideanGeometry3HomogenousPoint();
	std::vector<EuclideanGeometry3HomogenousPoint*> &getEuclideanGeometry3HomogenousPoints() { return EuclideanGeometry3HomogenousPoint_vec; }

	EuclideanGeometry3Vector * mkEuclideanGeometry3Vector(EuclideanGeometry* sp);
	EuclideanGeometry3Vector* mkEuclideanGeometry3Vector();
	std::vector<EuclideanGeometry3Vector*> &getEuclideanGeometry3Vectors() { return EuclideanGeometry3Vector_vec; }

	EuclideanGeometry3Scalar * mkEuclideanGeometry3Scalar(EuclideanGeometry* sp);
	EuclideanGeometry3Scalar* mkEuclideanGeometry3Scalar();
	std::vector<EuclideanGeometry3Scalar*> &getEuclideanGeometry3Scalars() { return EuclideanGeometry3Scalar_vec; }

	EuclideanGeometry3BasisChange * mkEuclideanGeometry3BasisChange(MapSpace* sp);
	EuclideanGeometry3BasisChange* mkEuclideanGeometry3BasisChange();
	std::vector<EuclideanGeometry3BasisChange*> &getEuclideanGeometry3BasisChanges() { return EuclideanGeometry3BasisChange_vec; }

	EuclideanGeometry3Scaling * mkEuclideanGeometry3Scaling(MapSpace* sp);
	EuclideanGeometry3Scaling* mkEuclideanGeometry3Scaling();
	std::vector<EuclideanGeometry3Scaling*> &getEuclideanGeometry3Scalings() { return EuclideanGeometry3Scaling_vec; }

	EuclideanGeometry3Shear * mkEuclideanGeometry3Shear(MapSpace* sp);
	EuclideanGeometry3Shear* mkEuclideanGeometry3Shear();
	std::vector<EuclideanGeometry3Shear*> &getEuclideanGeometry3Shears() { return EuclideanGeometry3Shear_vec; }

	ClassicalTime* mkClassicalTime(std::string key ,std::string name_);
	std::vector<ClassicalTime*> &getClassicalTimeSpaces() { return ClassicalTime_vec; }

	ClassicalTimeFrame* mkClassicalTimeFrame(std::string name, domain::ClassicalTime* space, domain::ClassicalTimeFrame* parent);
	ClassicalTimeFrameChange * mkClassicalTimeFrameChange(MapSpace* sp);
	ClassicalTimeFrameChange* mkClassicalTimeFrameChange();
	std::vector<ClassicalTimeFrameChange*> &getClassicalTimeFrameChanges() { return ClassicalTimeFrameChange_vec; }

	ClassicalTimePoint * mkClassicalTimePoint(ClassicalTime* sp);
	ClassicalTimePoint* mkClassicalTimePoint();
	std::vector<ClassicalTimePoint*> &getClassicalTimePoints() { return ClassicalTimePoint_vec; }

	ClassicalTimeHomogenousPoint * mkClassicalTimeHomogenousPoint(ClassicalTime* sp);
	ClassicalTimeHomogenousPoint* mkClassicalTimeHomogenousPoint();
	std::vector<ClassicalTimeHomogenousPoint*> &getClassicalTimeHomogenousPoints() { return ClassicalTimeHomogenousPoint_vec; }

	ClassicalTimeVector * mkClassicalTimeVector(ClassicalTime* sp);
	ClassicalTimeVector* mkClassicalTimeVector();
	std::vector<ClassicalTimeVector*> &getClassicalTimeVectors() { return ClassicalTimeVector_vec; }

	ClassicalTimeScalar * mkClassicalTimeScalar(ClassicalTime* sp);
	ClassicalTimeScalar* mkClassicalTimeScalar();
	std::vector<ClassicalTimeScalar*> &getClassicalTimeScalars() { return ClassicalTimeScalar_vec; }

	ClassicalTimeBasisChange * mkClassicalTimeBasisChange(MapSpace* sp);
	ClassicalTimeBasisChange* mkClassicalTimeBasisChange();
	std::vector<ClassicalTimeBasisChange*> &getClassicalTimeBasisChanges() { return ClassicalTimeBasisChange_vec; }

	ClassicalTimeScaling * mkClassicalTimeScaling(MapSpace* sp);
	ClassicalTimeScaling* mkClassicalTimeScaling();
	std::vector<ClassicalTimeScaling*> &getClassicalTimeScalings() { return ClassicalTimeScaling_vec; }

	ClassicalTimeShear * mkClassicalTimeShear(MapSpace* sp);
	ClassicalTimeShear* mkClassicalTimeShear();
	std::vector<ClassicalTimeShear*> &getClassicalTimeShears() { return ClassicalTimeShear_vec; }

	ClassicalVelocity* mkClassicalVelocity(std::string key ,std::string name_, int dimension_);
	std::vector<ClassicalVelocity*> &getClassicalVelocitySpaces() { return ClassicalVelocity_vec; }

	ClassicalVelocity3Frame* mkClassicalVelocity3Frame(std::string name, domain::ClassicalVelocity* space, domain::ClassicalVelocity3Frame* parent);
	ClassicalVelocity3Vector * mkClassicalVelocity3Vector(ClassicalVelocity* sp);
	ClassicalVelocity3Vector* mkClassicalVelocity3Vector();
	std::vector<ClassicalVelocity3Vector*> &getClassicalVelocity3Vectors() { return ClassicalVelocity3Vector_vec; }

	ClassicalVelocity3Scalar * mkClassicalVelocity3Scalar(ClassicalVelocity* sp);
	ClassicalVelocity3Scalar* mkClassicalVelocity3Scalar();
	std::vector<ClassicalVelocity3Scalar*> &getClassicalVelocity3Scalars() { return ClassicalVelocity3Scalar_vec; }

	ClassicalVelocity3BasisChange * mkClassicalVelocity3BasisChange(MapSpace* sp);
	ClassicalVelocity3BasisChange* mkClassicalVelocity3BasisChange();
	std::vector<ClassicalVelocity3BasisChange*> &getClassicalVelocity3BasisChanges() { return ClassicalVelocity3BasisChange_vec; }

	ClassicalVelocity3Scaling * mkClassicalVelocity3Scaling(MapSpace* sp);
	ClassicalVelocity3Scaling* mkClassicalVelocity3Scaling();
	std::vector<ClassicalVelocity3Scaling*> &getClassicalVelocity3Scalings() { return ClassicalVelocity3Scaling_vec; }

	ClassicalVelocity3Shear * mkClassicalVelocity3Shear(MapSpace* sp);
	ClassicalVelocity3Shear* mkClassicalVelocity3Shear();
	std::vector<ClassicalVelocity3Shear*> &getClassicalVelocity3Shears() { return ClassicalVelocity3Shear_vec; }

private:

	std::unordered_map<std::string, Space*> Space_map;
	std::vector<Space*> Space_vec;
	std::vector<EuclideanGeometry*> EuclideanGeometry_vec;
	std::vector<EuclideanGeometry3Rotation*>EuclideanGeometry3Rotation_vec;
	std::vector<EuclideanGeometry3Orientation*>EuclideanGeometry3Orientation_vec;
	std::vector<EuclideanGeometry3Angle*>EuclideanGeometry3Angle_vec;
	std::vector<EuclideanGeometry3FrameChange*>EuclideanGeometry3FrameChange_vec;
	std::vector<EuclideanGeometry3Point*>EuclideanGeometry3Point_vec;
	std::vector<EuclideanGeometry3HomogenousPoint*>EuclideanGeometry3HomogenousPoint_vec;
	std::vector<EuclideanGeometry3Vector*>EuclideanGeometry3Vector_vec;
	std::vector<EuclideanGeometry3Scalar*>EuclideanGeometry3Scalar_vec;
	std::vector<EuclideanGeometry3BasisChange*>EuclideanGeometry3BasisChange_vec;
	std::vector<EuclideanGeometry3Scaling*>EuclideanGeometry3Scaling_vec;
	std::vector<EuclideanGeometry3Shear*>EuclideanGeometry3Shear_vec;
	std::vector<ClassicalTime*> ClassicalTime_vec;
	std::vector<ClassicalTimeFrameChange*>ClassicalTimeFrameChange_vec;
	std::vector<ClassicalTimePoint*>ClassicalTimePoint_vec;
	std::vector<ClassicalTimeHomogenousPoint*>ClassicalTimeHomogenousPoint_vec;
	std::vector<ClassicalTimeVector*>ClassicalTimeVector_vec;
	std::vector<ClassicalTimeScalar*>ClassicalTimeScalar_vec;
	std::vector<ClassicalTimeBasisChange*>ClassicalTimeBasisChange_vec;
	std::vector<ClassicalTimeScaling*>ClassicalTimeScaling_vec;
	std::vector<ClassicalTimeShear*>ClassicalTimeShear_vec;
	std::vector<ClassicalVelocity*> ClassicalVelocity_vec;
	std::vector<ClassicalVelocity3Vector*>ClassicalVelocity3Vector_vec;
	std::vector<ClassicalVelocity3Scalar*>ClassicalVelocity3Scalar_vec;
	std::vector<ClassicalVelocity3BasisChange*>ClassicalVelocity3BasisChange_vec;
	std::vector<ClassicalVelocity3Scaling*>ClassicalVelocity3Scaling_vec;
	std::vector<ClassicalVelocity3Shear*>ClassicalVelocity3Shear_vec;
};


class Space {
public:
	Space() {};
    virtual ~Space(){};
	virtual std::string toString() const {
		return "Not implemented"; 
	}
    virtual std::string getName() const {
        return "Not implemented";
    }

    std::vector<Frame*> getFrames() const { return this->frames_; };
    void addFrame(Frame* frame);

protected:
    std::vector<Frame*> frames_;
};

class Frame {
public:
    Frame(std::string name, Space* space, Frame* parent) : name_(name), space_(space), parent_(parent) {};
    Frame() {};
    virtual ~Frame(){};
    virtual std::string toString() const {
        return "This is a mixin interface";
    }

    Frame* getParent() const{ return parent_; };
    void setParent(Frame* parent);

    std::string getName() const { return name_; };

    Space* getSpace() const { return space_; };

protected:
    Frame* parent_;
    Space* space_;
    std::string name_;

};



//pretend this is a union
class MapSpace : public Space {
public:
	MapSpace() {}
	MapSpace(domain::Space* domain, domain::Space* codomain) : domain_(domain), codomain_(codomain), change_space_{true}, change_frame_{true} {};

    MapSpace(domain::Space* domain, domain::Space* codomain, Frame* domain_frame, Frame* codomain_frame) 
        : domain_(domain), codomain_(codomain), domain_frame_(domain_frame), codomain_frame_(codomain_frame), change_space_{true}, change_frame_{true} {};

    MapSpace(domain::Space* domain, Frame* domain_frame, Frame* codomain_frame)
        : domain_(domain), codomain_(nullptr), domain_frame_(domain_frame), codomain_frame_(codomain_frame), change_space_{false}, change_frame_{true} {};
	std::string toString() const {
        return "@@Map(" + this->getName() + ")";
    };
    std::string getName() const{
        if(change_space_){
            if(change_frame_){
                return domain_->getName()+"."+domain_frame_->getName()+"->"+codomain_->getName()+"."+codomain_frame_->getName();
            }
            else{
                return domain_->getName()+"->"+codomain_->getName();
            }
        }
        else{
            if(change_frame_){
                return domain_->getName()+"."+domain_frame_->getName()+"->"+domain_->getName()+"."+codomain_frame_->getName();
            }
        }
        return "";
    }
        

	domain::Space* domain_;
	domain::Frame* domain_frame_;

    domain::Space* codomain_;
    domain::Frame* codomain_frame_;
    
    bool change_space_;
    bool change_frame_;
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
	std::string getName() const override { return name_; }; 
	int getDimension() const { return dimension_; }; 
    void addFrame(EuclideanGeometry3Frame* frame);
	std::string toString() const override {
		return "@@EuclideanGeometry  " + getName()   + "("+ std::to_string(getDimension()) + ")"; 
	}

private:
    std::string name_;
    int dimension_;
};


class EuclideanGeometry3Frame : public Frame {
public:
	EuclideanGeometry3Frame(std::string name,  EuclideanGeometry* space, EuclideanGeometry3Frame* parent) : Frame(name, space, parent) {};
	std::string toString() const override {
        std::string parentName = ((EuclideanGeometry*)this->space_)->getName();
		return "@@EuclideanGeometry3Frame  " + this->getName() + "(" + parentName + (this->parent_? "," + parentName + "." + this->parent_->getName() : "") + ")";
	}

private:
};


class EuclideanGeometry3Rotation : public DomainObject {
public:
    EuclideanGeometry3Rotation(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    EuclideanGeometry3Rotation(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~EuclideanGeometry3Rotation(){}
    std::string toString() override {
        return "@@EuclideanGeometry3Rotation(" + (space_?space_->getName():"Missing Space") + ")";
    }
    
    
    
private:
    EuclideanGeometry* space_; 
    
    
};


class EuclideanGeometry3Orientation : public DomainObject {
public:
    EuclideanGeometry3Orientation(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    EuclideanGeometry3Orientation(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~EuclideanGeometry3Orientation(){}
    std::string toString() override {
        return "@@EuclideanGeometry3Orientation(" + (space_?space_->getName():"Missing Space") + ")";
    }
    
    
    
private:
    EuclideanGeometry* space_; 
    
    
};


class EuclideanGeometry3Angle : public DomainObject {
public:
    EuclideanGeometry3Angle(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    EuclideanGeometry3Angle(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~EuclideanGeometry3Angle(){}
    std::string toString() override {
        return "@@EuclideanGeometry3Angle(" + (space_?space_->getName():"Missing Space") + ")";
    }
    
    
    
private:
    EuclideanGeometry* space_; 
    
    
};


class EuclideanGeometry3FrameChange : public DomainObject {
public:
    EuclideanGeometry3FrameChange(MapSpace* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    EuclideanGeometry3FrameChange(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~EuclideanGeometry3FrameChange(){}
    std::string toString() override {
        return "@@EuclideanGeometry3FrameChange(" + (space_?space_->getName():"Missing Space") + ")";
    }
    
    
    
private:
     
    
    MapSpace* space_;
};


class EuclideanGeometry3Point : public DomainObject {
public:
    EuclideanGeometry3Point(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    EuclideanGeometry3Point(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~EuclideanGeometry3Point(){}
    std::string toString() override {
        return "@@EuclideanGeometry3Point(" + (space_?space_->getName():"Missing Space")+","+(frame_?frame_->getName():"") + ")";
    }
    
    EuclideanGeometry3Frame* getFrame() const { return this->frame_; };
    void setFrame(EuclideanGeometry3Frame* frame);
private:
    EuclideanGeometry* space_; 
    EuclideanGeometry3Frame* frame_;
    
};


class EuclideanGeometry3HomogenousPoint : public DomainObject {
public:
    EuclideanGeometry3HomogenousPoint(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    EuclideanGeometry3HomogenousPoint(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~EuclideanGeometry3HomogenousPoint(){}
    std::string toString() override {
        return "@@EuclideanGeometry3HomogenousPoint(" + (space_?space_->getName():"Missing Space") + ")";
    }
    
    
    
private:
    EuclideanGeometry* space_; 
    
    
};


class EuclideanGeometry3Vector : public DomainObject {
public:
    EuclideanGeometry3Vector(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    EuclideanGeometry3Vector(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~EuclideanGeometry3Vector(){}
    std::string toString() override {
        return "@@EuclideanGeometry3Vector(" + (space_?space_->getName():"Missing Space")+","+(frame_?frame_->getName():"") + ")";
    }
    
    EuclideanGeometry3Frame* getFrame() const { return this->frame_; };
    void setFrame(EuclideanGeometry3Frame* frame);
private:
    EuclideanGeometry* space_; 
    EuclideanGeometry3Frame* frame_;
    
};


class EuclideanGeometry3Scalar : public DomainObject {
public:
    EuclideanGeometry3Scalar(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    EuclideanGeometry3Scalar(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~EuclideanGeometry3Scalar(){}
    std::string toString() override {
        return "@@EuclideanGeometry3Scalar(" + (space_?space_->getName():"Missing Space") + ")";
    }
    
    
    
private:
    EuclideanGeometry* space_; 
    
    
};


class EuclideanGeometry3BasisChange : public DomainObject {
public:
    EuclideanGeometry3BasisChange(MapSpace* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    EuclideanGeometry3BasisChange(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~EuclideanGeometry3BasisChange(){}
    std::string toString() override {
        return "@@EuclideanGeometry3BasisChange(" + (space_?space_->getName():"Missing Space") + ")";
    }
    
    
    
private:
     
    
    MapSpace* space_;
};


class EuclideanGeometry3Scaling : public DomainObject {
public:
    EuclideanGeometry3Scaling(MapSpace* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    EuclideanGeometry3Scaling(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~EuclideanGeometry3Scaling(){}
    std::string toString() override {
        return "@@EuclideanGeometry3Scaling(" + (space_?space_->getName():"Missing Space") + ")";
    }
    
    
    
private:
     
    
    MapSpace* space_;
};


class EuclideanGeometry3Shear : public DomainObject {
public:
    EuclideanGeometry3Shear(MapSpace* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    EuclideanGeometry3Shear(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~EuclideanGeometry3Shear(){}
    std::string toString() override {
        return "@@EuclideanGeometry3Shear(" + (space_?space_->getName():"Missing Space") + ")";
    }
    
    
    
private:
     
    
    MapSpace* space_;
};


class ClassicalTime : public Space {
public:
	ClassicalTime() : name_("") {};
	ClassicalTime(std::string name) : name_(name) {};
	
	std::string getName() const override { return name_; }; 
	
    void addFrame(ClassicalTimeFrame* frame);
	std::string toString() const override {
		return "@@ClassicalTime  " + getName()   + "(" + ")"; 
	}

private:
    std::string name_;
    
};


class ClassicalTimeFrame : public Frame {
public:
	ClassicalTimeFrame(std::string name,  ClassicalTime* space, ClassicalTimeFrame* parent) : Frame(name, space, parent) {};
	std::string toString() const override {
        std::string parentName = ((ClassicalTime*)this->space_)->getName();
		return "@@ClassicalTimeFrame  " + this->getName() + "(" + parentName + (this->parent_? "," + parentName + "." + this->parent_->getName() : "") + ")";
	}

private:
};


class ClassicalTimeFrameChange : public DomainObject {
public:
    ClassicalTimeFrameChange(MapSpace* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    ClassicalTimeFrameChange(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~ClassicalTimeFrameChange(){}
    std::string toString() override {
        return "@@ClassicalTimeFrameChange(" + (space_?space_->getName():"Missing Space") + ")";
    }
    
    
    
private:
     
    
    MapSpace* space_;
};


class ClassicalTimePoint : public DomainObject {
public:
    ClassicalTimePoint(ClassicalTime* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    ClassicalTimePoint(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~ClassicalTimePoint(){}
    std::string toString() override {
        return "@@ClassicalTimePoint(" + (space_?space_->getName():"Missing Space")+","+(frame_?frame_->getName():"") + ")";
    }
    
    ClassicalTimeFrame* getFrame() const { return this->frame_; };
    void setFrame(ClassicalTimeFrame* frame);
private:
    ClassicalTime* space_; 
    ClassicalTimeFrame* frame_;
    
};


class ClassicalTimeHomogenousPoint : public DomainObject {
public:
    ClassicalTimeHomogenousPoint(ClassicalTime* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    ClassicalTimeHomogenousPoint(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~ClassicalTimeHomogenousPoint(){}
    std::string toString() override {
        return "@@ClassicalTimeHomogenousPoint(" + (space_?space_->getName():"Missing Space") + ")";
    }
    
    
    
private:
    ClassicalTime* space_; 
    
    
};


class ClassicalTimeVector : public DomainObject {
public:
    ClassicalTimeVector(ClassicalTime* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    ClassicalTimeVector(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~ClassicalTimeVector(){}
    std::string toString() override {
        return "@@ClassicalTimeVector(" + (space_?space_->getName():"Missing Space")+","+(frame_?frame_->getName():"") + ")";
    }
    
    ClassicalTimeFrame* getFrame() const { return this->frame_; };
    void setFrame(ClassicalTimeFrame* frame);
private:
    ClassicalTime* space_; 
    ClassicalTimeFrame* frame_;
    
};


class ClassicalTimeScalar : public DomainObject {
public:
    ClassicalTimeScalar(ClassicalTime* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    ClassicalTimeScalar(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~ClassicalTimeScalar(){}
    std::string toString() override {
        return "@@ClassicalTimeScalar(" + (space_?space_->getName():"Missing Space") + ")";
    }
    
    
    
private:
    ClassicalTime* space_; 
    
    
};


class ClassicalTimeBasisChange : public DomainObject {
public:
    ClassicalTimeBasisChange(MapSpace* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    ClassicalTimeBasisChange(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~ClassicalTimeBasisChange(){}
    std::string toString() override {
        return "@@ClassicalTimeBasisChange(" + (space_?space_->getName():"Missing Space") + ")";
    }
    
    
    
private:
     
    
    MapSpace* space_;
};


class ClassicalTimeScaling : public DomainObject {
public:
    ClassicalTimeScaling(MapSpace* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    ClassicalTimeScaling(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~ClassicalTimeScaling(){}
    std::string toString() override {
        return "@@ClassicalTimeScaling(" + (space_?space_->getName():"Missing Space") + ")";
    }
    
    
    
private:
     
    
    MapSpace* space_;
};


class ClassicalTimeShear : public DomainObject {
public:
    ClassicalTimeShear(MapSpace* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    ClassicalTimeShear(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~ClassicalTimeShear(){}
    std::string toString() override {
        return "@@ClassicalTimeShear(" + (space_?space_->getName():"Missing Space") + ")";
    }
    
    
    
private:
     
    
    MapSpace* space_;
};


class ClassicalVelocity : public Space {
public:
	ClassicalVelocity() : name_("") {};
	ClassicalVelocity(std::string name) : name_(name) {};
	ClassicalVelocity(std::string name, int dimension) : name_(name), dimension_(dimension) {};
	std::string getName() const override { return name_; }; 
	int getDimension() const { return dimension_; }; 
    void addFrame(ClassicalVelocity3Frame* frame);
	std::string toString() const override {
		return "@@ClassicalVelocity  " + getName()   + "("+ std::to_string(getDimension()) + ")"; 
	}

private:
    std::string name_;
    int dimension_;
};


class ClassicalVelocity3Frame : public Frame {
public:
	ClassicalVelocity3Frame(std::string name,  ClassicalVelocity* space, ClassicalVelocity3Frame* parent) : Frame(name, space, parent) {};
	std::string toString() const override {
        std::string parentName = ((ClassicalVelocity*)this->space_)->getName();
		return "@@ClassicalVelocity3Frame  " + this->getName() + "(" + parentName + (this->parent_? "," + parentName + "." + this->parent_->getName() : "") + ")";
	}

private:
};


class ClassicalVelocity3Vector : public DomainObject {
public:
    ClassicalVelocity3Vector(ClassicalVelocity* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    ClassicalVelocity3Vector(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~ClassicalVelocity3Vector(){}
    std::string toString() override {
        return "@@ClassicalVelocity3Vector(" + (space_?space_->getName():"Missing Space")+","+(frame_?frame_->getName():"") + ")";
    }
    
    ClassicalVelocity3Frame* getFrame() const { return this->frame_; };
    void setFrame(ClassicalVelocity3Frame* frame);
private:
    ClassicalVelocity* space_; 
    ClassicalVelocity3Frame* frame_;
    
};


class ClassicalVelocity3Scalar : public DomainObject {
public:
    ClassicalVelocity3Scalar(ClassicalVelocity* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    ClassicalVelocity3Scalar(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~ClassicalVelocity3Scalar(){}
    std::string toString() override {
        return "@@ClassicalVelocity3Scalar(" + (space_?space_->getName():"Missing Space") + ")";
    }
    
    
    
private:
    ClassicalVelocity* space_; 
    
    
};


class ClassicalVelocity3BasisChange : public DomainObject {
public:
    ClassicalVelocity3BasisChange(MapSpace* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    ClassicalVelocity3BasisChange(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~ClassicalVelocity3BasisChange(){}
    std::string toString() override {
        return "@@ClassicalVelocity3BasisChange(" + (space_?space_->getName():"Missing Space") + ")";
    }
    
    
    
private:
     
    
    MapSpace* space_;
};


class ClassicalVelocity3Scaling : public DomainObject {
public:
    ClassicalVelocity3Scaling(MapSpace* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    ClassicalVelocity3Scaling(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~ClassicalVelocity3Scaling(){}
    std::string toString() override {
        return "@@ClassicalVelocity3Scaling(" + (space_?space_->getName():"Missing Space") + ")";
    }
    
    
    
private:
     
    
    MapSpace* space_;
};


class ClassicalVelocity3Shear : public DomainObject {
public:
    ClassicalVelocity3Shear(MapSpace* s, std::initializer_list<DomainObject*> args) : 
			domain::DomainObject(args), space_(s)  {}
    ClassicalVelocity3Shear(std::initializer_list<DomainObject*> args ) :
	 		domain::DomainObject(args) {}
	virtual ~ClassicalVelocity3Shear(){}
    std::string toString() override {
        return "@@ClassicalVelocity3Shear(" + (space_?space_->getName():"Missing Space") + ")";
    }
    
    
    
private:
     
    
    MapSpace* space_;
};

} // end namespace

#endif