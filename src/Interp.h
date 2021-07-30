#ifndef INTERP_H
#define INTERP_H

#include <cstddef>
#include <iostream> // for cheap logging only
#include <vector>
#include <utility>


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

class Location {
public:
    Location(int line_, int column_) : line(line_), column(column_) {};

    int getLine() const { return line; }
    int getColumn() const { return column; }

    std::string toString(){
        return std::string("Loc(") + std::to_string(line) + "," + std::to_string(column) + ")";
    }

    std::string toShortString(){
        return std::to_string(line)+","+std::to_string(column);
    }

private:
    int line;
    int column;
};

class OutputState {
public:
    OutputState(){

    }

    std::pair<std::shared_ptr<Location>,std::shared_ptr<Location>> update(std::string upd_str){
        int 
            cur_col = current_loc->getColumn(),
            cur_line = current_loc->getLine();
        
        int symb_ct = 0;
        for (std::string::size_type i = 0; i < upd_str.size(); i++) {
            if(upd_str[i] == '\n'){
                cur_line+=1;
                cur_col=1;
            }
            else if(upd_str[i] < 0){
                symb_ct += 1;
                if(i == upd_str.size() - 1)
                    cur_col += 1;
                else if(symb_ct == 3){
                    cur_col += 1;
                    symb_ct = 0;
                }
            }
            else{
                if(symb_ct >0){//don't put two symbols together :)
                    symb_ct = 0;
                    cur_col += 2;
                }
                else 
                    cur_col += 1;
            }
        }

        auto begin = current_loc;
        auto end = std::make_shared<Location>(Location(cur_line, cur_col));
        this->current_loc = end;
        this->current_output += upd_str;
        return std::make_pair<std::shared_ptr<Location>,std::shared_ptr<Location>>(
                std::forward<std::shared_ptr<Location>>(begin),
                std::forward<std::shared_ptr<Location>>(end));
    };

    std::string getOutput(){
        return this->current_output;
    }

    std::shared_ptr<Location> getCurrentLoc(){
        return this->current_loc;
    }

    std::string printState(){
        return current_loc->toString() + "\n" + current_output + "\n";
    }

    void reset(){
        current_output = "";
        current_loc = std::make_shared<Location>(1,1);
    }

private:
    std::string current_output;
    std::shared_ptr<Location> current_loc;
};

class Interp {
public:
    Interp(coords::Coords* coords_, domain::DomainContainer* domain_, std::vector<Interp*> operands_) 
        : coords(coords_),domain(domain_),operands(operands_),linked(nullptr),container(nullptr), constructor(nullptr) {};
    Interp(coords::Coords* coords_, domain::DomainContainer* domain_, std::vector<Interp*> operands_, std::vector<Interp*> body_) 
        : coords(coords_),domain(domain_),operands(operands_),body(body_), linked(nullptr),container(nullptr), constructor(nullptr) {};
    std::string toString();
    std::string toStringAST(std::vector<domain::CoordinateSpace*> spaces, std::vector<domain::TimeSeries*> series);

    void buildString(bool withType=true);

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
    bool hasLinked() {
        return (linked);
    }
    interp::Interp* getLinked() const {
        return linked;
    }
    void addLink(interp::Interp* interp_){
        this->links.push_back(interp_);
    };
    void setLinked(interp::Interp* interp_){
        this->linked = interp_;
    }
    bool hasContainer() {
        return (container);
    }
    interp::Interp* getContainer() const {
        return container;
    }
    void addProperty(interp::Interp* prop_){
        this->properties.push_back(prop_);
    };
    void setContainer(interp::Interp* container_){
        this->container = container_;
    }
    void setConstructor(interp::Interp* interp_){
        this->constructor = interp_;
    }

    bool hasValue();
    domain::DomainObject* getValue();
    std::string getType();

    void setStartLocation(std::shared_ptr<interp::Location> pos){
        this->start_location = pos;
    }

    void setEndLocation(std::shared_ptr<interp::Location> pos){
        this->end_location = pos;
    }

    std::shared_ptr<interp::Location> getStartLocation(){
        return this->start_location;
    }

    std::shared_ptr<interp::Location> getEndLocation(){
        return this->end_location;
    }

protected:
    coords::Coords* coords;
    domain::DomainContainer* domain;
    std::vector<Interp*> operands;
    std::vector<Interp*> body;
    std::vector<interp::Interp*> links;
    std::vector<interp::Interp*> properties;
    interp::Interp* linked;
    interp::Interp* constructor;
    interp::Interp* container;
    std::shared_ptr<Location> start_location;
    std::shared_ptr<Location> end_location;
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