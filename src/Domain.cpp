
#include <vector>
#include <iostream>
#include <string>
#include <utility>

// DONE: Separate clients from Domain
// #include "Checker.h"

#include "Domain.h"

//#include <g3log/g3log.hpp>

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

DomainContainer::DomainContainer(std::initializer_list<DomainObject*> operands) : DomainObject(operands) {
    this->inner_ = nullptr;
    this->as_ = AnnotationState::Unannotated;
};

DomainContainer::DomainContainer(std::vector<DomainObject*> operands) : DomainObject(operands) {
    this->inner_ = nullptr;
    this->as_ = AnnotationState::Unannotated;
};
DomainContainer::DomainContainer(std::initializer_list<DomainContainer*> operands) {
    for(auto dom : operands){
        operands_.push_back((DomainObject*)dom);
    }
    operand_count = this->operands_.size();
    this->inner_ = nullptr;
    this->as_ = AnnotationState::Unannotated;
};

DomainContainer::DomainContainer(std::vector<DomainContainer*> operands) {
    for(auto dom : operands){
        operands_.push_back((DomainObject*)dom);
    }
    operand_count = this->operands_.size();
    this->inner_ = nullptr;
    this->as_ = AnnotationState::Unannotated;
};



void DomainContainer::setValue(DomainObject* dom_){

    //dom_->setOperands(this->inner_->getOperands());
    
    /*
    WARNING - THIS IS NOT CORRECT CODE. YOU ALSO NEED TO UNMAP/ERASE FROM THE "OBJECT_VEC". DO THIS SOON! 7/12
    */
    //these are getting cached and potentially reused now, don't delete
    //delete this->inner_;

    this->inner_ = dom_;
};

bool DomainContainer::hasValue() const{
    return this->inner_ != nullptr;
};

std::string DomainContainer::toString() const{
    if(this->hasValue()){
        return this->inner_->toString();
    }
    else{
        return "No Interpretation provided";
    }
};

DomainContainer* Domain::mkDefaultDomainContainer(){
    return new domain::DomainContainer();
};

DomainContainer* Domain::mkDefaultDomainContainer(std::initializer_list<DomainContainer*> operands){
    return new domain::DomainContainer(operands);
};

DomainContainer* Domain::mkDefaultDomainContainer(std::vector<DomainContainer*> operands){
    return new domain::DomainContainer(operands);
};

/*

    StandardTimeCoordinateSpace* mkStandardTimeCoordinateSpace(string name);
    DerivedTimeCoordinateSpace* mkDerivedTimeCoordinateSpace(string name, TimeCoordinateSpace* parent, float* originData, float** basisData);

    Duration* mkDuration(string name, TimeCoordinateSpace* parent, float* value);
    Time* mkTime(string name, TimeCoordinateSpace* parent, float* value);

*/

StandardTimeCoordinateSpace* Domain::mkStandardTimeCoordinateSpace(std::string name){
    StandardTimeCoordinateSpace* sp = new StandardTimeCoordinateSpace(name);
    this->spaces.push_back(static_cast<TimeCoordinateSpace*>(sp));
    this->timeSpaces.push_back(sp);
    return sp;
};

DerivedTimeCoordinateSpace* Domain::mkDerivedTimeCoordinateSpace(std::string name, TimeCoordinateSpace* parent, float* originData, float** basisData){
    DerivedTimeCoordinateSpace* sp = new DerivedTimeCoordinateSpace(name, parent, originData, basisData);
    this->spaces.push_back(static_cast<TimeCoordinateSpace*>(sp));
    this->timeSpaces.push_back(sp);
    return sp;
};
StandardGeom1DCoordinateSpace* Domain::mkStandardGeom1DCoordinateSpace(std::string name){
    StandardGeom1DCoordinateSpace* sp = new StandardGeom1DCoordinateSpace(name);
    this->spaces.push_back(static_cast<Geom1DCoordinateSpace*>(sp));
    this->geom1dSpaces.push_back(sp);
    return sp;
};

DerivedGeom1DCoordinateSpace* Domain::mkDerivedGeom1DCoordinateSpace(std::string name, Geom1DCoordinateSpace* parent, float* originData, float** basisData){
    DerivedGeom1DCoordinateSpace* sp = new DerivedGeom1DCoordinateSpace(name, parent, originData, basisData);
    this->spaces.push_back(static_cast<Geom1DCoordinateSpace*>(sp));
    this->geom1dSpaces.push_back(sp);
    return sp;
};

Scalar* Domain::mkScalar(std::string name, float* value){
    auto scalar = new Scalar(name, value);
    return scalar;
}

Duration* Domain::mkDuration(std::string name, TimeCoordinateSpace* parent, float* value){
    auto dur = new Duration(name, parent, value);
    return dur;
}

Time* Domain::mkTime(std::string name, TimeCoordinateSpace* parent, float* value){
    auto time = new Time(name, parent, value);
    return time;
}

TimeTransform* Domain::mkTimeTransform(std::string name, TimeCoordinateSpace* domain_, TimeCoordinateSpace* codomain_){
    auto ttransform = new TimeTransform(name, domain_, codomain_);
    return ttransform;
}

Displacement* Domain::mkDisplacement(std::string name, Geom1DCoordinateSpace* parent, float* value){
    auto disp = new Displacement(name, parent, value);
    return disp;
}

Position* Domain::mkPosition(std::string name, Geom1DCoordinateSpace* parent, float* value){
    auto pos = new Position(name, parent, value);
    return pos;
}

Geom1DTransform* Domain::mkGeom1DTransform(std::string name, Geom1DCoordinateSpace* domain_, Geom1DCoordinateSpace* codomain_){
    auto g1transform = new Geom1DTransform(name, domain_, codomain_);
    return g1transform;
}
