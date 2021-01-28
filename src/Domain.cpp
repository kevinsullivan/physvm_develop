
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
/*
void Frame::setParent(Frame* parent){
    this->parent_ = parent;
};*/

void DerivedFrame::setParent(Frame* parent){
    this->parent_ = parent;
};
void AliasedFrame::setAliased(Frame* original){
    this->original_ = original;
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
/*
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
	if(auto dc = dynamic_cast<domain::EuclideanGeometry3*>(space)){
            if(auto df = dynamic_cast<domain::EuclideanGeometry3Frame*>(parent)){
            auto child = this->mkEuclideanGeometry3Frame(name, dc, df);
            return child;
        }
    }
	if(auto dc = dynamic_cast<domain::ClassicalVelocity*>(space)){
            if(auto df = dynamic_cast<domain::ClassicalVelocityFrame*>(parent)){
            auto child = this->mkClassicalVelocityFrame(name, dc, df);
            return child;
        }
    }
    return nullptr;
};
*/
/*Frame* Domain::mkFrame(std::string name, Space* space, Frame* parent){
    

};*/
/*
template<Space* sp> 
Frame<sp>* mkAliasedFrame(std::string name, Frame* aliased){
    var frm = new domain::AliasedFrame<sp>(name, aliased);
    sp->addFrame(frm);
    return frm;
};

template<Space* sp>
Frame<sp>* mkDerivedFrame(std::string name, Frame* parent){
    var frm = new domain::DerivedFrame<sp>(name, parent);
    sp->addFrame(frm);
    return frm;
};
*/


SIMeasurementSystem* Domain::mkSIMeasurementSystem(std::string name){
    auto si = new SIMeasurementSystem(name);
    this->measurementSystems.push_back(si);
    return si;
};

ImperialMeasurementSystem* Domain::mkImperialMeasurementSystem(std::string name){
    auto imp = new ImperialMeasurementSystem(name);
    this->measurementSystems.push_back(imp);
    return imp;

};



MapSpace* Domain::mkMapSpace(Space* space, Frame* dom, Frame* cod){
    return new MapSpace(space, dom, cod);
};

EuclideanGeometry* Domain::mkEuclideanGeometry(std::string key,std::string name_, int dimension_){
        EuclideanGeometry* s = new EuclideanGeometry(name_, dimension_);
        //s->addFrame(new domain::EuclideanGeometryFrame("Standard", s, nullptr));
        s->addFrame(new domain::EuclideanGeometryStandardFrame(s));
        this->EuclideanGeometry_vec.push_back(s);
        this->Space_vec.push_back(s);
        this->Space_map[key] = s;
    
        return s;
    };

//std::vector<EuclideanGeometry*> &Domain::getEuclideanGeometrySpaces() { return EuclideanGeometry_vec; }

EuclideanGeometryAliasedFrame* Domain::mkEuclideanGeometryAliasedFrame(std::string name, domain::EuclideanGeometry* space, domain::EuclideanGeometryFrame* parent, domain::MeasurementSystem* ms){
    EuclideanGeometryAliasedFrame* child = new domain::EuclideanGeometryAliasedFrame(name, space, parent,ms);
    space->addFrame(child);
    return child;
}
            

EuclideanGeometryDerivedFrame* Domain::mkEuclideanGeometryDerivedFrame(std::string name, domain::EuclideanGeometry* space, domain::EuclideanGeometryFrame* parent){
    EuclideanGeometryDerivedFrame* child = new domain::EuclideanGeometryDerivedFrame(name, space, parent);
    space->addFrame(child);
    return child;
}
            

/*void EuclideanGeometry::addFrame(EuclideanGeometryFrame* frame){
    ((Space*)this)->addFrame(frame);
}*/
void EuclideanGeometry::addFrame(EuclideanGeometryFrame* frame){
    ((Space*)this)->addFrame(frame);
}

ClassicalTime* Domain::mkClassicalTime(std::string key,std::string name_){
        ClassicalTime* s = new ClassicalTime(name_);
        //s->addFrame(new domain::ClassicalTimeFrame("Standard", s, nullptr));
        s->addFrame(new domain::ClassicalTimeStandardFrame(s));
        this->ClassicalTime_vec.push_back(s);
        this->Space_vec.push_back(s);
        this->Space_map[key] = s;
    
        return s;
    };

//std::vector<ClassicalTime*> &Domain::getClassicalTimeSpaces() { return ClassicalTime_vec; }

ClassicalTimeAliasedFrame* Domain::mkClassicalTimeAliasedFrame(std::string name, domain::ClassicalTime* space, domain::ClassicalTimeFrame* parent, domain::MeasurementSystem* ms){
    ClassicalTimeAliasedFrame* child = new domain::ClassicalTimeAliasedFrame(name, space, parent,ms);
    space->addFrame(child);
    return child;
}
            

ClassicalTimeDerivedFrame* Domain::mkClassicalTimeDerivedFrame(std::string name, domain::ClassicalTime* space, domain::ClassicalTimeFrame* parent){
    ClassicalTimeDerivedFrame* child = new domain::ClassicalTimeDerivedFrame(name, space, parent);
    space->addFrame(child);
    return child;
}
            

/*void ClassicalTime::addFrame(ClassicalTimeFrame* frame){
    ((Space*)this)->addFrame(frame);
}*/
void ClassicalTime::addFrame(ClassicalTimeFrame* frame){
    ((Space*)this)->addFrame(frame);
}

EuclideanGeometry3* Domain::mkEuclideanGeometry3(std::string key,std::string name_){
        EuclideanGeometry3* s = new EuclideanGeometry3(name_);
        //s->addFrame(new domain::EuclideanGeometry3Frame("Standard", s, nullptr));
        s->addFrame(new domain::EuclideanGeometry3StandardFrame(s));
        this->EuclideanGeometry3_vec.push_back(s);
        this->Space_vec.push_back(s);
        this->Space_map[key] = s;
    
        return s;
    };

//std::vector<EuclideanGeometry3*> &Domain::getEuclideanGeometry3Spaces() { return EuclideanGeometry3_vec; }

EuclideanGeometry3AliasedFrame* Domain::mkEuclideanGeometry3AliasedFrame(std::string name, domain::EuclideanGeometry3* space, domain::EuclideanGeometry3Frame* parent, domain::MeasurementSystem* ms){
    EuclideanGeometry3AliasedFrame* child = new domain::EuclideanGeometry3AliasedFrame(name, space, parent,ms);
    space->addFrame(child);
    return child;
}
            

EuclideanGeometry3DerivedFrame* Domain::mkEuclideanGeometry3DerivedFrame(std::string name, domain::EuclideanGeometry3* space, domain::EuclideanGeometry3Frame* parent){
    EuclideanGeometry3DerivedFrame* child = new domain::EuclideanGeometry3DerivedFrame(name, space, parent);
    space->addFrame(child);
    return child;
}
            

/*void EuclideanGeometry3::addFrame(EuclideanGeometry3Frame* frame){
    ((Space*)this)->addFrame(frame);
}*/
void EuclideanGeometry3::addFrame(EuclideanGeometry3Frame* frame){
    ((Space*)this)->addFrame(frame);
}

ClassicalVelocity* Domain::mkClassicalVelocity(std::string key,std::string name_, Space* base1, Space* base2){
        ClassicalVelocity* s = new ClassicalVelocity(name_, base1, base2);
        s->addFrame(new domain::ClassicalVelocityStandardFrame(s));
        this->ClassicalVelocity_vec.push_back(s);
        this->Space_vec.push_back(s);
        this->Space_map[key] = s;
    
        return s;
    };

//std::vector<ClassicalVelocity*> &Domain::getClassicalVelocitySpaces() { return ClassicalVelocity_vec; }

ClassicalVelocityAliasedFrame* Domain::mkClassicalVelocityAliasedFrame(std::string name, domain::ClassicalVelocity* space, domain::ClassicalVelocityFrame* parent, domain::MeasurementSystem* ms){
    ClassicalVelocityAliasedFrame* child = new domain::ClassicalVelocityAliasedFrame(name, space, parent,ms);
    space->addFrame(child);
    return child;
}
            

ClassicalVelocityDerivedFrame* Domain::mkClassicalVelocityDerivedFrame(std::string name, domain::ClassicalVelocity* space, domain::ClassicalVelocityFrame* parent){
    ClassicalVelocityDerivedFrame* child = new domain::ClassicalVelocityDerivedFrame(name, space, parent);
    space->addFrame(child);
    return child;
}
            

/*void ClassicalVelocity::addFrame(ClassicalVelocityFrame* frame){
    ((Space*)this)->addFrame(frame);
}*/
void ClassicalVelocity::addFrame(ClassicalVelocityFrame* frame){
    ((Space*)this)->addFrame(frame);
}
