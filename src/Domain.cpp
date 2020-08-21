
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
            if(auto df = dynamic_cast<domain::EuclideanGeometryFrame*>(parent)){
            auto child = this->mkEuclideanGeometryFrame(name, dc, df);
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
            if(auto df = dynamic_cast<domain::ClassicalVelocityFrame*>(parent)){
            auto child = this->mkClassicalVelocityFrame(name, dc, df);
            return child;
        }
    }
	if(auto dc = dynamic_cast<domain::ClassicalAcceleration*>(space)){
            if(auto df = dynamic_cast<domain::ClassicalAccelerationFrame*>(parent)){
            auto child = this->mkClassicalAccelerationFrame(name, dc, df);
            return child;
        }
    }
    return nullptr;
};



MapSpace* Domain::mkMapSpace(Space* space, Frame* dom, Frame* cod){
    return new MapSpace(space, dom, cod);
};

EuclideanGeometry* Domain::mkEuclideanGeometry(std::string key,std::string name_, int dimension_){
        EuclideanGeometry* s = new EuclideanGeometry(name_, dimension_);
        s->addFrame(new domain::EuclideanGeometryFrame("Standard", s, nullptr));
        this->EuclideanGeometry_vec.push_back(s);
        this->Space_vec.push_back(s);
        this->Space_map[key] = s;
    
        return s;
    };

//std::vector<EuclideanGeometry*> &Domain::getEuclideanGeometrySpaces() { return EuclideanGeometry_vec; }

EuclideanGeometryFrame* Domain::mkEuclideanGeometryFrame(std::string name, domain::EuclideanGeometry* space, domain::EuclideanGeometryFrame* parent){
    EuclideanGeometryFrame* child = new domain::EuclideanGeometryFrame(name, space, parent);
    space->addFrame(child);
    return child;
}
            

void EuclideanGeometry::addFrame(EuclideanGeometryFrame* frame){
    ((Space*)this)->addFrame(frame);
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

ClassicalVelocity* Domain::mkClassicalVelocity(std::string key,std::string name_, Space* base1, Space* base2){
        ClassicalVelocity* s = new ClassicalVelocity(name_, base1, base2);
        s->addFrame(new domain::ClassicalVelocityFrame("Standard", s, nullptr));
        this->ClassicalVelocity_vec.push_back(s);
        this->Space_vec.push_back(s);
        this->Space_map[key] = s;
    
        return s;
    };

//std::vector<ClassicalVelocity*> &Domain::getClassicalVelocitySpaces() { return ClassicalVelocity_vec; }

ClassicalVelocityFrame* Domain::mkClassicalVelocityFrame(std::string name, domain::ClassicalVelocity* space, domain::ClassicalVelocityFrame* parent){
    ClassicalVelocityFrame* child = new domain::ClassicalVelocityFrame(name, space, parent);
    space->addFrame(child);
    return child;
}
            

void ClassicalVelocity::addFrame(ClassicalVelocityFrame* frame){
    ((Space*)this)->addFrame(frame);
}

ClassicalAcceleration* Domain::mkClassicalAcceleration(std::string key,std::string name_, Space* base1, Space* base2){
        ClassicalAcceleration* s = new ClassicalAcceleration(name_, base1, base2);
        s->addFrame(new domain::ClassicalAccelerationFrame("Standard", s, nullptr));
        this->ClassicalAcceleration_vec.push_back(s);
        this->Space_vec.push_back(s);
        this->Space_map[key] = s;
    
        return s;
    };

//std::vector<ClassicalAcceleration*> &Domain::getClassicalAccelerationSpaces() { return ClassicalAcceleration_vec; }

ClassicalAccelerationFrame* Domain::mkClassicalAccelerationFrame(std::string name, domain::ClassicalAcceleration* space, domain::ClassicalAccelerationFrame* parent){
    ClassicalAccelerationFrame* child = new domain::ClassicalAccelerationFrame(name, space, parent);
    space->addFrame(child);
    return child;
}
            

void ClassicalAcceleration::addFrame(ClassicalAccelerationFrame* frame){
    ((Space*)this)->addFrame(frame);
}
