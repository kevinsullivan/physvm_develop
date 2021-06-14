#ifndef INTERP_H
#define INTERP_H

#include <cstddef>
#include <iostream> // for cheap logging only
#include <vector>

#include "Coords.h"
//#include "AST.h"
#include "Domain.h"

/*
namespace interp2domain
{
    class InterpToDomain;
}
#ifndef INTERP2DOMAIN_H
#include "InterpToDomain.h"
#endif
*/
namespace interp{

class Interp {
public:
    Interp(coords::Coords* coords_, domain::DomainContainer* domain_, std::vector<Interp*> operands_) 
        : coords(coords_),domain(domain_),operands(operands_),linked(nullptr),constructor(nullptr) {};
    Interp(coords::Coords* coords_, domain::DomainContainer* domain_, std::vector<Interp*> operands_, std::vector<Interp*> body_) 
        : coords(coords_),domain(domain_),operands(operands_),body(body_), linked(nullptr),constructor(nullptr) {};
    std::string toString();
    std::string toStringLinked(std::vector<domain::CoordinateSpace*> spaces);

    std::string toDefString(){
        return "def " + this->toString();
    }

    std::string toLetString(){
        return "let " + this->toString() + " in";
    }

    Interp* getOperand(int i) const {
        return this->operands[i];
    }
    domain::DomainContainer* getDomain() const {
        return this->domain;
    }
    coords::Coords* getCoords() const {
        return this->coords;
    }
    bool hasLink() {
        return (linked);
    }
    interp::Interp* getLink() const {
        return linked;
    }
    void addLink(interp::Interp* interp_){
        this->links.push_back(interp_);
    };
    void setLinked(interp::Interp* interp_){
        this->linked = interp_;
    }
    void setConstructor(interp::Interp* interp_){
        this->constructor = interp_;
    }

    bool hasValue();
    std::string getType();
protected:
    coords::Coords* coords;
    domain::DomainContainer* domain;
    std::vector<Interp*> operands;
    std::vector<Interp*> body;
    std::vector<interp::Interp*> links;
    interp::Interp* linked;
    interp::Interp* constructor;
};

class COMPOUND_STMT : public Interp {

};

class DECL_INIT_R1 : public Interp {

};

class DECL_LIST_R1 : public Interp {

};

class APPEND_LIST_R1 : public Interp {

};

class LIT_R1 : public Interp {

};

class IDENT_R1 : public Interp {

};

class REF_R1 : public Interp {

};

class ADD_R1_R1 : public Interp {

};

class MUL_R1_R1 : public Interp {

};

/*
if (nodeType =="COMPOUND_STMT") {
        for(auto op: operands){
            retval+= op->toString() + "\n";
        }
    } 
    else if(nodeType == "DECL_INIT_R1") {
        auto var_ = (this->operands[0]);
        auto expr_ = (this->operands[1]);
        auto vardom_ = var_->getDomain();
        
        retval += std::string("def ") + this->coords->getName() + " : " + (var_->getType()) + " := " + expr_->toString();//[(" +  + ")]";
    }
    else if(nodeType == "DECL_LIST_R1") {
        auto var_ = (this->operands[0]);
        retval += std::string("def ") + this->coords->getName() + std::to_string(ident_++) + " : " + (var_->getType()) + " := []";
    }
    else if(nodeType == "APPEND_LIST_R1") {
        auto val_ = (this->operands[0]);

        retval += std::string("def ") + this->coords->getName() + std::to_string(ident_++) + " : " + (var_->getType()) + " := " + this->coords->getName() + std::to_string(ident_++) + " ++ [" + val_->toString() + "]";
    }
    else if(nodeType == "LIT_R1") {
        if(this->domain->hasValue()){
            retval += "[";
            if(auto astime = dynamic_cast<domain::Time*>(this->domain->getValue())){
                retval+= std::string("mk_time ") + astime->getSpace()->getName() + ".value " + std::to_string(astime->getValue()[0]);
            }
            else if(auto asdur = dynamic_cast<domain::Duration*>(this->domain->getValue())){
                retval+= std::string("mk_duration ") + asdur->getSpace()->getName() + ".value " + std::to_string(asdur->getValue()[0]);
            }
            else if(auto asscalar = dynamic_cast<domain::Scalar*>(this->domain->getValue())){
                retval+= std::string("(") + std::to_string(asscalar->getValue()[0]) + " : F)";
            }
            else if(auto astrans = dynamic_cast<domain::TimeTransform*>(this->domain->getValue())){
                auto dom_ = astrans->getDomain();
                auto cod_ = astrans->getCodomain();
                retval+= dom_->getName() + ".value.mk_time_transform_to " + cod_->getName() + ".value";
            }
            retval += "]";
        }
        else{
            return "_";
        }
    } 
    else if(nodeType == "IDENT_R1") {
        retval += this->coords->getName();
    }
    else if(nodeType == "REF_R1") {
        retval += this->coords->getLinked()->getName();
        //if(this->domain->hasValue())
        //    retval += this->domain->getValue()->getName();
    } 
    else if(nodeType == "ADD_R1_R1") {
        auto lhs_ = (this->operands[0]);
        auto rhs_ = (this->operands[1]);
        retval += lhs_->toString() + "+ᵥ" + rhs_->toString();
    }
    else if(nodeType == "MUL_R1_R1") {

*/


}

#endif