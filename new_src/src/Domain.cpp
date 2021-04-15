
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

DomainContainer::DomainContainer(std::initializer_list<DomainObject*> operands) : DomainObject(operands) {
    this->inner_ = nullptr;
};

DomainContainer::DomainContainer(std::vector<DomainObject*> operands) : DomainObject(operands) {
    this->inner_ = nullptr;
};
DomainContainer::DomainContainer(std::initializer_list<DomainContainer*> operands) {
    for(auto dom : operands){
        operands_.push_back((DomainObject*)dom);
    }
    operand_count = this->operands_.size();
    this->inner_ = nullptr;
};

DomainContainer::DomainContainer(std::vector<DomainContainer*> operands) {
    for(auto dom : operands){
        operands_.push_back((DomainObject*)dom);
    }
    operand_count = this->operands_.size();
    this->inner_ = nullptr;
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

Duration* Domain::mkDuration(std::string name, TimeCoordinateSpace* parent, float* value){
    auto dur = new Duration(name, parent, value);
    return dur;
}

Time* Domain::mkTime(std::string name, TimeCoordinateSpace* parent, float* value){
    auto time = new Time(name, parent, value);
    return time;
}

