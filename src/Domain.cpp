
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

DomainObject* Domain::mkDefaultDomainContainer(){
    return new domain::DomainContainer();
};

DomainObject* Domain::mkDefaultDomainContainer(std::initializer_list<DomainObject*> operands){
    return new domain::DomainContainer(operands);
};

DomainObject* Domain::mkDefaultDomainContainer(std::vector<DomainObject*> operands){
    return new domain::DomainContainer(operands);
};


EuclideanGeometry* Domain::mkEuclideanGeometry(std::string key,std::string name_, int dimension_){
    EuclideanGeometry* s = new EuclideanGeometry(name_, dimension_);
    this->EuclideanGeometry_vec.push_back(s);
    this->Space_vec.push_back(s);
    this->Space_map[key] = s;
    return s;
}

//std::vector<EuclideanGeometry*> &Domain::getEuclideanGeometrySpaces() { return EuclideanGeometry_vec; }

Geometric3Rotation* Domain::mkGeometric3Rotation(EuclideanGeometry* sp){
    Geometric3Rotation* dom_ = new Geometric3Rotation(sp, {});
    this->Geometric3Rotation_vec.push_back(dom_);
    return dom_;
}
                
Geometric3Rotation* Domain::mkGeometric3Rotation(){
    Geometric3Rotation* dom_ = new Geometric3Rotation({});
    this->Geometric3Rotation_vec.push_back(dom_);   
    return dom_;
}

Geometric3Orientation* Domain::mkGeometric3Orientation(EuclideanGeometry* sp){
    Geometric3Orientation* dom_ = new Geometric3Orientation(sp, {});
    this->Geometric3Orientation_vec.push_back(dom_);
    return dom_;
}
                
Geometric3Orientation* Domain::mkGeometric3Orientation(){
    Geometric3Orientation* dom_ = new Geometric3Orientation({});
    this->Geometric3Orientation_vec.push_back(dom_);   
    return dom_;
}

Geometric3Angle* Domain::mkGeometric3Angle(EuclideanGeometry* sp){
    Geometric3Angle* dom_ = new Geometric3Angle(sp, {});
    this->Geometric3Angle_vec.push_back(dom_);
    return dom_;
}
                
Geometric3Angle* Domain::mkGeometric3Angle(){
    Geometric3Angle* dom_ = new Geometric3Angle({});
    this->Geometric3Angle_vec.push_back(dom_);   
    return dom_;
}

Geometric3FrameChange* Domain::mkGeometric3FrameChange(EuclideanGeometry* sp){
    Geometric3FrameChange* dom_ = new Geometric3FrameChange(sp, {});
    this->Geometric3FrameChange_vec.push_back(dom_);
    return dom_;
}
                
Geometric3FrameChange* Domain::mkGeometric3FrameChange(){
    Geometric3FrameChange* dom_ = new Geometric3FrameChange({});
    this->Geometric3FrameChange_vec.push_back(dom_);   
    return dom_;
}

Geometric3Point* Domain::mkGeometric3Point(EuclideanGeometry* sp){
    Geometric3Point* dom_ = new Geometric3Point(sp, {});
    this->Geometric3Point_vec.push_back(dom_);
    return dom_;
}
                
Geometric3Point* Domain::mkGeometric3Point(){
    Geometric3Point* dom_ = new Geometric3Point({});
    this->Geometric3Point_vec.push_back(dom_);   
    return dom_;
}

Geometric3HomogenousPoint* Domain::mkGeometric3HomogenousPoint(EuclideanGeometry* sp){
    Geometric3HomogenousPoint* dom_ = new Geometric3HomogenousPoint(sp, {});
    this->Geometric3HomogenousPoint_vec.push_back(dom_);
    return dom_;
}
                
Geometric3HomogenousPoint* Domain::mkGeometric3HomogenousPoint(){
    Geometric3HomogenousPoint* dom_ = new Geometric3HomogenousPoint({});
    this->Geometric3HomogenousPoint_vec.push_back(dom_);   
    return dom_;
}

Geometric3Vector* Domain::mkGeometric3Vector(EuclideanGeometry* sp){
    Geometric3Vector* dom_ = new Geometric3Vector(sp, {});
    this->Geometric3Vector_vec.push_back(dom_);
    return dom_;
}
                
Geometric3Vector* Domain::mkGeometric3Vector(){
    Geometric3Vector* dom_ = new Geometric3Vector({});
    this->Geometric3Vector_vec.push_back(dom_);   
    return dom_;
}

Geometric3Scalar* Domain::mkGeometric3Scalar(EuclideanGeometry* sp){
    Geometric3Scalar* dom_ = new Geometric3Scalar(sp, {});
    this->Geometric3Scalar_vec.push_back(dom_);
    return dom_;
}
                
Geometric3Scalar* Domain::mkGeometric3Scalar(){
    Geometric3Scalar* dom_ = new Geometric3Scalar({});
    this->Geometric3Scalar_vec.push_back(dom_);   
    return dom_;
}

Geometric3BasisChange* Domain::mkGeometric3BasisChange(EuclideanGeometry* sp){
    Geometric3BasisChange* dom_ = new Geometric3BasisChange(sp, {});
    this->Geometric3BasisChange_vec.push_back(dom_);
    return dom_;
}
                
Geometric3BasisChange* Domain::mkGeometric3BasisChange(){
    Geometric3BasisChange* dom_ = new Geometric3BasisChange({});
    this->Geometric3BasisChange_vec.push_back(dom_);   
    return dom_;
}

Geometric3Scaling* Domain::mkGeometric3Scaling(EuclideanGeometry* sp){
    Geometric3Scaling* dom_ = new Geometric3Scaling(sp, {});
    this->Geometric3Scaling_vec.push_back(dom_);
    return dom_;
}
                
Geometric3Scaling* Domain::mkGeometric3Scaling(){
    Geometric3Scaling* dom_ = new Geometric3Scaling({});
    this->Geometric3Scaling_vec.push_back(dom_);   
    return dom_;
}

Geometric3Shear* Domain::mkGeometric3Shear(EuclideanGeometry* sp){
    Geometric3Shear* dom_ = new Geometric3Shear(sp, {});
    this->Geometric3Shear_vec.push_back(dom_);
    return dom_;
}
                
Geometric3Shear* Domain::mkGeometric3Shear(){
    Geometric3Shear* dom_ = new Geometric3Shear({});
    this->Geometric3Shear_vec.push_back(dom_);   
    return dom_;
}

ClassicalTime* Domain::mkClassicalTime(std::string key,std::string name_){
    ClassicalTime* s = new ClassicalTime(name_);
    this->ClassicalTime_vec.push_back(s);
    this->Space_vec.push_back(s);
    this->Space_map[key] = s;
    return s;
}

//std::vector<ClassicalTime*> &Domain::getClassicalTimeSpaces() { return ClassicalTime_vec; }

TimeFrameChange* Domain::mkTimeFrameChange(ClassicalTime* sp){
    TimeFrameChange* dom_ = new TimeFrameChange(sp, {});
    this->TimeFrameChange_vec.push_back(dom_);
    return dom_;
}
                
TimeFrameChange* Domain::mkTimeFrameChange(){
    TimeFrameChange* dom_ = new TimeFrameChange({});
    this->TimeFrameChange_vec.push_back(dom_);   
    return dom_;
}

TimePoint* Domain::mkTimePoint(ClassicalTime* sp){
    TimePoint* dom_ = new TimePoint(sp, {});
    this->TimePoint_vec.push_back(dom_);
    return dom_;
}
                
TimePoint* Domain::mkTimePoint(){
    TimePoint* dom_ = new TimePoint({});
    this->TimePoint_vec.push_back(dom_);   
    return dom_;
}

TimeHomogenousPoint* Domain::mkTimeHomogenousPoint(ClassicalTime* sp){
    TimeHomogenousPoint* dom_ = new TimeHomogenousPoint(sp, {});
    this->TimeHomogenousPoint_vec.push_back(dom_);
    return dom_;
}
                
TimeHomogenousPoint* Domain::mkTimeHomogenousPoint(){
    TimeHomogenousPoint* dom_ = new TimeHomogenousPoint({});
    this->TimeHomogenousPoint_vec.push_back(dom_);   
    return dom_;
}

TimeVector* Domain::mkTimeVector(ClassicalTime* sp){
    TimeVector* dom_ = new TimeVector(sp, {});
    this->TimeVector_vec.push_back(dom_);
    return dom_;
}
                
TimeVector* Domain::mkTimeVector(){
    TimeVector* dom_ = new TimeVector({});
    this->TimeVector_vec.push_back(dom_);   
    return dom_;
}

TimeScalar* Domain::mkTimeScalar(ClassicalTime* sp){
    TimeScalar* dom_ = new TimeScalar(sp, {});
    this->TimeScalar_vec.push_back(dom_);
    return dom_;
}
                
TimeScalar* Domain::mkTimeScalar(){
    TimeScalar* dom_ = new TimeScalar({});
    this->TimeScalar_vec.push_back(dom_);   
    return dom_;
}

TimeBasisChange* Domain::mkTimeBasisChange(ClassicalTime* sp){
    TimeBasisChange* dom_ = new TimeBasisChange(sp, {});
    this->TimeBasisChange_vec.push_back(dom_);
    return dom_;
}
                
TimeBasisChange* Domain::mkTimeBasisChange(){
    TimeBasisChange* dom_ = new TimeBasisChange({});
    this->TimeBasisChange_vec.push_back(dom_);   
    return dom_;
}

TimeScaling* Domain::mkTimeScaling(ClassicalTime* sp){
    TimeScaling* dom_ = new TimeScaling(sp, {});
    this->TimeScaling_vec.push_back(dom_);
    return dom_;
}
                
TimeScaling* Domain::mkTimeScaling(){
    TimeScaling* dom_ = new TimeScaling({});
    this->TimeScaling_vec.push_back(dom_);   
    return dom_;
}

TimeShear* Domain::mkTimeShear(ClassicalTime* sp){
    TimeShear* dom_ = new TimeShear(sp, {});
    this->TimeShear_vec.push_back(dom_);
    return dom_;
}
                
TimeShear* Domain::mkTimeShear(){
    TimeShear* dom_ = new TimeShear({});
    this->TimeShear_vec.push_back(dom_);   
    return dom_;
}

ClassicalVelocity* Domain::mkClassicalVelocity(std::string key,std::string name_, int dimension_){
    ClassicalVelocity* s = new ClassicalVelocity(name_, dimension_);
    this->ClassicalVelocity_vec.push_back(s);
    this->Space_vec.push_back(s);
    this->Space_map[key] = s;
    return s;
}

//std::vector<ClassicalVelocity*> &Domain::getClassicalVelocitySpaces() { return ClassicalVelocity_vec; }

Velocity3Vector* Domain::mkVelocity3Vector(ClassicalVelocity* sp){
    Velocity3Vector* dom_ = new Velocity3Vector(sp, {});
    this->Velocity3Vector_vec.push_back(dom_);
    return dom_;
}
                
Velocity3Vector* Domain::mkVelocity3Vector(){
    Velocity3Vector* dom_ = new Velocity3Vector({});
    this->Velocity3Vector_vec.push_back(dom_);   
    return dom_;
}

Velocity3Scalar* Domain::mkVelocity3Scalar(ClassicalVelocity* sp){
    Velocity3Scalar* dom_ = new Velocity3Scalar(sp, {});
    this->Velocity3Scalar_vec.push_back(dom_);
    return dom_;
}
                
Velocity3Scalar* Domain::mkVelocity3Scalar(){
    Velocity3Scalar* dom_ = new Velocity3Scalar({});
    this->Velocity3Scalar_vec.push_back(dom_);   
    return dom_;
}

Velocity3BasisChange* Domain::mkVelocity3BasisChange(ClassicalVelocity* sp){
    Velocity3BasisChange* dom_ = new Velocity3BasisChange(sp, {});
    this->Velocity3BasisChange_vec.push_back(dom_);
    return dom_;
}
                
Velocity3BasisChange* Domain::mkVelocity3BasisChange(){
    Velocity3BasisChange* dom_ = new Velocity3BasisChange({});
    this->Velocity3BasisChange_vec.push_back(dom_);   
    return dom_;
}

Velocity3Scaling* Domain::mkVelocity3Scaling(ClassicalVelocity* sp){
    Velocity3Scaling* dom_ = new Velocity3Scaling(sp, {});
    this->Velocity3Scaling_vec.push_back(dom_);
    return dom_;
}
                
Velocity3Scaling* Domain::mkVelocity3Scaling(){
    Velocity3Scaling* dom_ = new Velocity3Scaling({});
    this->Velocity3Scaling_vec.push_back(dom_);   
    return dom_;
}

Velocity3Shear* Domain::mkVelocity3Shear(ClassicalVelocity* sp){
    Velocity3Shear* dom_ = new Velocity3Shear(sp, {});
    this->Velocity3Shear_vec.push_back(dom_);
    return dom_;
}
                
Velocity3Shear* Domain::mkVelocity3Shear(){
    Velocity3Shear* dom_ = new Velocity3Shear({});
    this->Velocity3Shear_vec.push_back(dom_);   
    return dom_;
}
