
#include <vector>
#include <iostream>
#include <string>
#include <utility>

// DONE: Separate clients from Domain
// #include "Checker.h"

#include "Domain.h"

#include <g3log/g3log.hpp>

#ifndef leanInferenceWildcard
#define leanInferenceWildcard "_"
#endif

using namespace std;
using namespace domain;


DomainObject::DomainObject(std::initializer_list<DomainObject*> args) {
    for(auto dom : args){
        operands_.push_back(dom);
    }
    operand_count = this->operands_.size();
}
DomainObject* DomainObject::getOperand(int i) { return this->operands_.at(i); };
void DomainObject::setOperands(std::vector<DomainObject*> operands) { this->operands_ = operands; };
std::string DomainObject::toString(){return "A generic, default DomainObject"; };
std::vector<Space*> &Domain::getSpaces() 
{
    return Space_vec; 
};



DomainContainer::DomainContainer(std::initializer_list<DomainObject*> operands) : DomainObject(operands) {
    this->inner_ = nullptr;
};

DomainContainer::DomainContainer(std::vector<DomainObject*> operands) : DomainObject(operands) {
    this->inner_ = nullptr;
};


void DomainContainer::setValue(DomainObject* dom_){

    //dom_->setOperands(this->inner_->getOperands());
    
    /*
    WARNING - THIS IS NOT CORRECT CODE. YOU ALSO NEED TO UNMAP/ERASE FROM THE "OBJECT_VEC". DO THIS SOON! 7/12
    */

    delete this->inner_;

    this->inner_ = dom_;
};

bool DomainContainer::hasValue(){
    return (bool)this->inner_;
};

std::string DomainContainer::toString(){
    if(this->hasValue()){
        return this->inner_->toString();
    }
    else{
        return "No Interpretation provided";
    }
};



Space* Domain::getSpace(std::string key){
    return this->Space_map[key];
};

void Space::addFrame(Frame* frame){
    this->frames_.push_back(frame);
};

void Frame::setParent(Frame* parent){
    this->parent_ = parent;
};

DomainObject* Domain::mkDefaultDomainContainer(){
    return new domain::DomainContainer();
};

DomainObject* Domain::mkDefaultDomainContainer(std::initializer_list<DomainObject*> operands){
    return new domain::DomainContainer(operands);
};

DomainObject* Domain::mkDefaultDomainContainer(std::vector<DomainObject*> operands){
    return new domain::DomainContainer(operands);
};

Frame* Domain::mkFrame(std::string name, Space* space, Frame* parent){
    
	if(auto dc = dynamic_cast<domain::EuclideanGeometry*>(space)){
            if(auto df = dynamic_cast<domain::EuclideanGeometry3Frame*>(parent)){
            auto child = this->mkEuclideanGeometry3Frame(name, dc, df);
            return child;
        }
    }
	if(auto dc = dynamic_cast<domain::ClassicalTime*>(space)){
            if(auto df = dynamic_cast<domain::ClassicalTimeFrame*>(parent)){
            auto child = this->mkClassicalTimeFrame(name, dc, df);
            return child;
        }
    }
	if(auto dc = dynamic_cast<domain::ClassicalVelocity*>(space)){
            if(auto df = dynamic_cast<domain::ClassicalVelocity3Frame*>(parent)){
            auto child = this->mkClassicalVelocity3Frame(name, dc, df);
            return child;
        }
    }
};



MapSpace* Domain::mkMapSpace(Space* space, Frame* dom, Frame* cod){
    return new MapSpace(space, dom, cod);
};

EuclideanGeometry* Domain::mkEuclideanGeometry(std::string key,std::string name_, int dimension_){
    EuclideanGeometry* s = new EuclideanGeometry(name_, dimension_);
    s->addFrame(new domain::EuclideanGeometry3Frame("Standard", s, nullptr));
    this->EuclideanGeometry_vec.push_back(s);
    this->Space_vec.push_back(s);
    this->Space_map[key] = s;
    
    return s;
};

//std::vector<EuclideanGeometry*> &Domain::getEuclideanGeometrySpaces() { return EuclideanGeometry_vec; }

EuclideanGeometry3Frame* Domain::mkEuclideanGeometry3Frame(std::string name, domain::EuclideanGeometry* space, domain::EuclideanGeometry3Frame* parent){
    EuclideanGeometry3Frame* child = new domain::EuclideanGeometry3Frame(name, space, parent);
    space->addFrame(child);
    return child;
}
            

void EuclideanGeometry::addFrame(EuclideanGeometry3Frame* frame){
    ((Space*)this)->addFrame(frame);
}

EuclideanGeometry3Rotation* Domain::mkEuclideanGeometry3Rotation(EuclideanGeometry* sp){
    EuclideanGeometry3Rotation* dom_ = new EuclideanGeometry3Rotation(sp, {});
    this->EuclideanGeometry3Rotation_vec.push_back(dom_);
    return dom_;
}
                
EuclideanGeometry3Rotation* Domain::mkEuclideanGeometry3Rotation(){
    EuclideanGeometry3Rotation* dom_ = new EuclideanGeometry3Rotation({});
    this->EuclideanGeometry3Rotation_vec.push_back(dom_);   
    return dom_;
}

EuclideanGeometry3Orientation* Domain::mkEuclideanGeometry3Orientation(EuclideanGeometry* sp){
    EuclideanGeometry3Orientation* dom_ = new EuclideanGeometry3Orientation(sp, {});
    this->EuclideanGeometry3Orientation_vec.push_back(dom_);
    return dom_;
}
                
EuclideanGeometry3Orientation* Domain::mkEuclideanGeometry3Orientation(){
    EuclideanGeometry3Orientation* dom_ = new EuclideanGeometry3Orientation({});
    this->EuclideanGeometry3Orientation_vec.push_back(dom_);   
    return dom_;
}

EuclideanGeometry3Angle* Domain::mkEuclideanGeometry3Angle(EuclideanGeometry* sp){
    EuclideanGeometry3Angle* dom_ = new EuclideanGeometry3Angle(sp, {});
    this->EuclideanGeometry3Angle_vec.push_back(dom_);
    return dom_;
}
                
EuclideanGeometry3Angle* Domain::mkEuclideanGeometry3Angle(){
    EuclideanGeometry3Angle* dom_ = new EuclideanGeometry3Angle({});
    this->EuclideanGeometry3Angle_vec.push_back(dom_);   
    return dom_;
}

EuclideanGeometry3FrameChange* Domain::mkEuclideanGeometry3FrameChange(MapSpace* sp){
    EuclideanGeometry3FrameChange* dom_ = new EuclideanGeometry3FrameChange(sp, {});
    this->EuclideanGeometry3FrameChange_vec.push_back(dom_);
    return dom_;
}
                
EuclideanGeometry3FrameChange* Domain::mkEuclideanGeometry3FrameChange(){
    EuclideanGeometry3FrameChange* dom_ = new EuclideanGeometry3FrameChange({});
    this->EuclideanGeometry3FrameChange_vec.push_back(dom_);   
    return dom_;
}

EuclideanGeometry3Point* Domain::mkEuclideanGeometry3Point(EuclideanGeometry* sp){
    EuclideanGeometry3Point* dom_ = new EuclideanGeometry3Point(sp, {});
    this->EuclideanGeometry3Point_vec.push_back(dom_);
    return dom_;
}
                
EuclideanGeometry3Point* Domain::mkEuclideanGeometry3Point(){
    EuclideanGeometry3Point* dom_ = new EuclideanGeometry3Point({});
    this->EuclideanGeometry3Point_vec.push_back(dom_);   
    return dom_;
}

void EuclideanGeometry3Point::setFrame(EuclideanGeometry3Frame* frame){
    this->frame_ = frame;
};
EuclideanGeometry3HomogenousPoint* Domain::mkEuclideanGeometry3HomogenousPoint(EuclideanGeometry* sp){
    EuclideanGeometry3HomogenousPoint* dom_ = new EuclideanGeometry3HomogenousPoint(sp, {});
    this->EuclideanGeometry3HomogenousPoint_vec.push_back(dom_);
    return dom_;
}
                
EuclideanGeometry3HomogenousPoint* Domain::mkEuclideanGeometry3HomogenousPoint(){
    EuclideanGeometry3HomogenousPoint* dom_ = new EuclideanGeometry3HomogenousPoint({});
    this->EuclideanGeometry3HomogenousPoint_vec.push_back(dom_);   
    return dom_;
}

EuclideanGeometry3Vector* Domain::mkEuclideanGeometry3Vector(EuclideanGeometry* sp){
    EuclideanGeometry3Vector* dom_ = new EuclideanGeometry3Vector(sp, {});
    this->EuclideanGeometry3Vector_vec.push_back(dom_);
    return dom_;
}
                
EuclideanGeometry3Vector* Domain::mkEuclideanGeometry3Vector(){
    EuclideanGeometry3Vector* dom_ = new EuclideanGeometry3Vector({});
    this->EuclideanGeometry3Vector_vec.push_back(dom_);   
    return dom_;
}

void EuclideanGeometry3Vector::setFrame(EuclideanGeometry3Frame* frame){
    this->frame_ = frame;
};
EuclideanGeometry3Scalar* Domain::mkEuclideanGeometry3Scalar(EuclideanGeometry* sp){
    EuclideanGeometry3Scalar* dom_ = new EuclideanGeometry3Scalar(sp, {});
    this->EuclideanGeometry3Scalar_vec.push_back(dom_);
    return dom_;
}
                
EuclideanGeometry3Scalar* Domain::mkEuclideanGeometry3Scalar(){
    EuclideanGeometry3Scalar* dom_ = new EuclideanGeometry3Scalar({});
    this->EuclideanGeometry3Scalar_vec.push_back(dom_);   
    return dom_;
}

EuclideanGeometry3BasisChange* Domain::mkEuclideanGeometry3BasisChange(MapSpace* sp){
    EuclideanGeometry3BasisChange* dom_ = new EuclideanGeometry3BasisChange(sp, {});
    this->EuclideanGeometry3BasisChange_vec.push_back(dom_);
    return dom_;
}
                
EuclideanGeometry3BasisChange* Domain::mkEuclideanGeometry3BasisChange(){
    EuclideanGeometry3BasisChange* dom_ = new EuclideanGeometry3BasisChange({});
    this->EuclideanGeometry3BasisChange_vec.push_back(dom_);   
    return dom_;
}

EuclideanGeometry3Scaling* Domain::mkEuclideanGeometry3Scaling(MapSpace* sp){
    EuclideanGeometry3Scaling* dom_ = new EuclideanGeometry3Scaling(sp, {});
    this->EuclideanGeometry3Scaling_vec.push_back(dom_);
    return dom_;
}
                
EuclideanGeometry3Scaling* Domain::mkEuclideanGeometry3Scaling(){
    EuclideanGeometry3Scaling* dom_ = new EuclideanGeometry3Scaling({});
    this->EuclideanGeometry3Scaling_vec.push_back(dom_);   
    return dom_;
}

EuclideanGeometry3Shear* Domain::mkEuclideanGeometry3Shear(MapSpace* sp){
    EuclideanGeometry3Shear* dom_ = new EuclideanGeometry3Shear(sp, {});
    this->EuclideanGeometry3Shear_vec.push_back(dom_);
    return dom_;
}
                
EuclideanGeometry3Shear* Domain::mkEuclideanGeometry3Shear(){
    EuclideanGeometry3Shear* dom_ = new EuclideanGeometry3Shear({});
    this->EuclideanGeometry3Shear_vec.push_back(dom_);   
    return dom_;
}

ClassicalTime* Domain::mkClassicalTime(std::string key,std::string name_){
    ClassicalTime* s = new ClassicalTime(name_);
    s->addFrame(new domain::ClassicalTimeFrame("Standard", s, nullptr));
    this->ClassicalTime_vec.push_back(s);
    this->Space_vec.push_back(s);
    this->Space_map[key] = s;
    
    return s;
};

//std::vector<ClassicalTime*> &Domain::getClassicalTimeSpaces() { return ClassicalTime_vec; }

ClassicalTimeFrame* Domain::mkClassicalTimeFrame(std::string name, domain::ClassicalTime* space, domain::ClassicalTimeFrame* parent){
    ClassicalTimeFrame* child = new domain::ClassicalTimeFrame(name, space, parent);
    space->addFrame(child);
    return child;
}
            

void ClassicalTime::addFrame(ClassicalTimeFrame* frame){
    ((Space*)this)->addFrame(frame);
}

ClassicalTimeFrameChange* Domain::mkClassicalTimeFrameChange(MapSpace* sp){
    ClassicalTimeFrameChange* dom_ = new ClassicalTimeFrameChange(sp, {});
    this->ClassicalTimeFrameChange_vec.push_back(dom_);
    return dom_;
}
                
ClassicalTimeFrameChange* Domain::mkClassicalTimeFrameChange(){
    ClassicalTimeFrameChange* dom_ = new ClassicalTimeFrameChange({});
    this->ClassicalTimeFrameChange_vec.push_back(dom_);   
    return dom_;
}

ClassicalTimePoint* Domain::mkClassicalTimePoint(ClassicalTime* sp){
    ClassicalTimePoint* dom_ = new ClassicalTimePoint(sp, {});
    this->ClassicalTimePoint_vec.push_back(dom_);
    return dom_;
}
                
ClassicalTimePoint* Domain::mkClassicalTimePoint(){
    ClassicalTimePoint* dom_ = new ClassicalTimePoint({});
    this->ClassicalTimePoint_vec.push_back(dom_);   
    return dom_;
}

void ClassicalTimePoint::setFrame(ClassicalTimeFrame* frame){
    this->frame_ = frame;
};
ClassicalTimeHomogenousPoint* Domain::mkClassicalTimeHomogenousPoint(ClassicalTime* sp){
    ClassicalTimeHomogenousPoint* dom_ = new ClassicalTimeHomogenousPoint(sp, {});
    this->ClassicalTimeHomogenousPoint_vec.push_back(dom_);
    return dom_;
}
                
ClassicalTimeHomogenousPoint* Domain::mkClassicalTimeHomogenousPoint(){
    ClassicalTimeHomogenousPoint* dom_ = new ClassicalTimeHomogenousPoint({});
    this->ClassicalTimeHomogenousPoint_vec.push_back(dom_);   
    return dom_;
}

ClassicalTimeVector* Domain::mkClassicalTimeVector(ClassicalTime* sp){
    ClassicalTimeVector* dom_ = new ClassicalTimeVector(sp, {});
    this->ClassicalTimeVector_vec.push_back(dom_);
    return dom_;
}
                
ClassicalTimeVector* Domain::mkClassicalTimeVector(){
    ClassicalTimeVector* dom_ = new ClassicalTimeVector({});
    this->ClassicalTimeVector_vec.push_back(dom_);   
    return dom_;
}

void ClassicalTimeVector::setFrame(ClassicalTimeFrame* frame){
    this->frame_ = frame;
};
ClassicalTimeScalar* Domain::mkClassicalTimeScalar(ClassicalTime* sp){
    ClassicalTimeScalar* dom_ = new ClassicalTimeScalar(sp, {});
    this->ClassicalTimeScalar_vec.push_back(dom_);
    return dom_;
}
                
ClassicalTimeScalar* Domain::mkClassicalTimeScalar(){
    ClassicalTimeScalar* dom_ = new ClassicalTimeScalar({});
    this->ClassicalTimeScalar_vec.push_back(dom_);   
    return dom_;
}

ClassicalTimeBasisChange* Domain::mkClassicalTimeBasisChange(MapSpace* sp){
    ClassicalTimeBasisChange* dom_ = new ClassicalTimeBasisChange(sp, {});
    this->ClassicalTimeBasisChange_vec.push_back(dom_);
    return dom_;
}
                
ClassicalTimeBasisChange* Domain::mkClassicalTimeBasisChange(){
    ClassicalTimeBasisChange* dom_ = new ClassicalTimeBasisChange({});
    this->ClassicalTimeBasisChange_vec.push_back(dom_);   
    return dom_;
}

ClassicalTimeScaling* Domain::mkClassicalTimeScaling(MapSpace* sp){
    ClassicalTimeScaling* dom_ = new ClassicalTimeScaling(sp, {});
    this->ClassicalTimeScaling_vec.push_back(dom_);
    return dom_;
}
                
ClassicalTimeScaling* Domain::mkClassicalTimeScaling(){
    ClassicalTimeScaling* dom_ = new ClassicalTimeScaling({});
    this->ClassicalTimeScaling_vec.push_back(dom_);   
    return dom_;
}

ClassicalTimeShear* Domain::mkClassicalTimeShear(MapSpace* sp){
    ClassicalTimeShear* dom_ = new ClassicalTimeShear(sp, {});
    this->ClassicalTimeShear_vec.push_back(dom_);
    return dom_;
}
                
ClassicalTimeShear* Domain::mkClassicalTimeShear(){
    ClassicalTimeShear* dom_ = new ClassicalTimeShear({});
    this->ClassicalTimeShear_vec.push_back(dom_);   
    return dom_;
}

ClassicalVelocity* Domain::mkClassicalVelocity(std::string key,std::string name_, int dimension_){
    ClassicalVelocity* s = new ClassicalVelocity(name_, dimension_);
    s->addFrame(new domain::ClassicalVelocity3Frame("Standard", s, nullptr));
    this->ClassicalVelocity_vec.push_back(s);
    this->Space_vec.push_back(s);
    this->Space_map[key] = s;
    
    return s;
};

//std::vector<ClassicalVelocity*> &Domain::getClassicalVelocitySpaces() { return ClassicalVelocity_vec; }

ClassicalVelocity3Frame* Domain::mkClassicalVelocity3Frame(std::string name, domain::ClassicalVelocity* space, domain::ClassicalVelocity3Frame* parent){
    ClassicalVelocity3Frame* child = new domain::ClassicalVelocity3Frame(name, space, parent);
    space->addFrame(child);
    return child;
}
            

void ClassicalVelocity::addFrame(ClassicalVelocity3Frame* frame){
    ((Space*)this)->addFrame(frame);
}

ClassicalVelocity3Vector* Domain::mkClassicalVelocity3Vector(ClassicalVelocity* sp){
    ClassicalVelocity3Vector* dom_ = new ClassicalVelocity3Vector(sp, {});
    this->ClassicalVelocity3Vector_vec.push_back(dom_);
    return dom_;
}
                
ClassicalVelocity3Vector* Domain::mkClassicalVelocity3Vector(){
    ClassicalVelocity3Vector* dom_ = new ClassicalVelocity3Vector({});
    this->ClassicalVelocity3Vector_vec.push_back(dom_);   
    return dom_;
}

void ClassicalVelocity3Vector::setFrame(ClassicalVelocity3Frame* frame){
    this->frame_ = frame;
};
ClassicalVelocity3Scalar* Domain::mkClassicalVelocity3Scalar(ClassicalVelocity* sp){
    ClassicalVelocity3Scalar* dom_ = new ClassicalVelocity3Scalar(sp, {});
    this->ClassicalVelocity3Scalar_vec.push_back(dom_);
    return dom_;
}
                
ClassicalVelocity3Scalar* Domain::mkClassicalVelocity3Scalar(){
    ClassicalVelocity3Scalar* dom_ = new ClassicalVelocity3Scalar({});
    this->ClassicalVelocity3Scalar_vec.push_back(dom_);   
    return dom_;
}

ClassicalVelocity3BasisChange* Domain::mkClassicalVelocity3BasisChange(MapSpace* sp){
    ClassicalVelocity3BasisChange* dom_ = new ClassicalVelocity3BasisChange(sp, {});
    this->ClassicalVelocity3BasisChange_vec.push_back(dom_);
    return dom_;
}
                
ClassicalVelocity3BasisChange* Domain::mkClassicalVelocity3BasisChange(){
    ClassicalVelocity3BasisChange* dom_ = new ClassicalVelocity3BasisChange({});
    this->ClassicalVelocity3BasisChange_vec.push_back(dom_);   
    return dom_;
}

ClassicalVelocity3Scaling* Domain::mkClassicalVelocity3Scaling(MapSpace* sp){
    ClassicalVelocity3Scaling* dom_ = new ClassicalVelocity3Scaling(sp, {});
    this->ClassicalVelocity3Scaling_vec.push_back(dom_);
    return dom_;
}
                
ClassicalVelocity3Scaling* Domain::mkClassicalVelocity3Scaling(){
    ClassicalVelocity3Scaling* dom_ = new ClassicalVelocity3Scaling({});
    this->ClassicalVelocity3Scaling_vec.push_back(dom_);   
    return dom_;
}

ClassicalVelocity3Shear* Domain::mkClassicalVelocity3Shear(MapSpace* sp){
    ClassicalVelocity3Shear* dom_ = new ClassicalVelocity3Shear(sp, {});
    this->ClassicalVelocity3Shear_vec.push_back(dom_);
    return dom_;
}
                
ClassicalVelocity3Shear* Domain::mkClassicalVelocity3Shear(){
    ClassicalVelocity3Shear* dom_ = new ClassicalVelocity3Shear({});
    this->ClassicalVelocity3Shear_vec.push_back(dom_);   
    return dom_;
}
