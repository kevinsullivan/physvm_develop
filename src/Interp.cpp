#include "Interp.h"

#include "Domain.h"

//#include <g3log/g3log.hpp>

#include <algorithm>
#include <unordered_map>
#include <vector>

//using namespace g3; 

namespace interp{

int ident_ = 0;
std::unordered_map<Interp*, int> ident_map;

/*
Work in progress, move much of this to configuration with some templates
*/
std::string Interp::toString(){
    std::string retval = "";
    std::string nodeType = this->coords->getNodeType();
    //std::cout<<nodeType<<"\n";
    
    if (nodeType =="COMPOUND_STMT") {
        for(auto op: operands){
            retval+= op->toString() + "\n";
        }
    } 
    else if(nodeType == "DECL_INIT_R1") {
        auto var_ = (this->operands[0]);
        auto expr_ = (this->operands[1]);
        auto vardom_ = var_->getDomain();
        //std::cout<<"COORDNM\n";
        //std::cout<<this->coords->getName()<<"\n";
        //std::cout<<this->coords->hasName()<<"\n";
        //std::cout<<this->coords->state_->name_<<"\n";
        retval += std::string("def ") + this->coords->getName()/*(vardom_->hasValue() ? vardom_->getValue()->getName() : "")*/ + " : " + (var_->getType()) + " := " + expr_->toString();//[(" +  + ")]";
    }
    else if(nodeType == "DECL_LIST_R1") {
        auto var_ = (this->operands[0]);
        auto iident_ = ident_map.count(var_) ? (ident_map[var_] = ident_map[var_]++) : (ident_map[var_] = ident_++);
        retval += std::string("def ") + this->coords->getName() + std::to_string(iident_) + " : list (" + (var_->getType()) + ") := []";
    }
    else if(nodeType == "APPEND_LIST_R1") {
        auto val_ = (this->operands[0]);
        auto iident_ = ident_map.count(this) ? (ident_map[this] = ident_map[this]++) : (ident_map[this] = ident_++);
        retval += std::string("def ") + this->coords->getLinked()->getName() + std::to_string(iident_) + " : list (" + (this->getType()) + ") := " + this->coords->getLinked()->getName() + std::to_string(iident_-1) + " ++ [" + val_->toString() + "]";
    }
    else if(nodeType == "LIT_R1") {
        
        if(this->constructor and this->constructor->hasValue()){
            retval += "( ";
        }

        if(this->domain->hasValue()){
            /*
                Move this into config as well
            */


            retval += "|";
            if(auto astime = dynamic_cast<domain::Time*>(this->domain->getValue())){
                retval+= std::string("mk_time ") + astime->getSpace()->getName() + ".value " + std::to_string(astime->getValue()[0]);
            }
            else if(auto asdur = dynamic_cast<domain::Duration*>(this->domain->getValue())){
                retval+= std::string("mk_duration ") + asdur->getSpace()->getName() + ".value " + std::to_string(asdur->getValue()[0]);
            }
            else if(auto asscalar = dynamic_cast<domain::Scalar*>(this->domain->getValue())){
                retval+= std::string("(") + std::to_string(asscalar->getValue()[0]) + " : scalar)";
            }
            else if(auto astrans = dynamic_cast<domain::TimeTransform*>(this->domain->getValue())){
                auto dom_ = astrans->getDomain();
                auto cod_ = astrans->getCodomain();
                retval+= dom_->getName() + ".value.mk_time_transform_to " + cod_->getName() + ".value";
            }
            else if(auto aspos = dynamic_cast<domain::Position*>(this->domain->getValue())){
                retval+= std::string("mk_position ") + astime->getSpace()->getName() + ".value " + std::to_string(astime->getValue()[0]);
            }
            else if(auto asdisp = dynamic_cast<domain::Displacement*>(this->domain->getValue())){
                retval+= std::string("mk_displacement ") + asdur->getSpace()->getName() + ".value " + std::to_string(asdur->getValue()[0]);
            }
            else if(auto astrans = dynamic_cast<domain::Geom1DTransform*>(this->domain->getValue())){
                auto dom_ = astrans->getDomain();
                auto cod_ = astrans->getCodomain();
                retval+= dom_->getName() + ".value.mk_geom1d_transform_to " + cod_->getName() + ".value";
            }
            retval += "|";

        }
        else{
            retval += "_";
        }
        
        if(this->constructor and this->constructor->hasValue()){
            retval += " : " + this->constructor->getType() + ")";
        }
    } 
    else if(nodeType == "IDENT_R1") {
        retval += this->coords->getName();
    }
    else if(nodeType == "IDENT_LIST_R1") {
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
        auto lhs_ = (this->operands[0]);
        auto rhs_ = (this->operands[1]);

        if(lhs_->getDomain()->hasValue()){
            
            if(auto astrans = dynamic_cast<domain::TimeTransform*>(lhs_->getDomain()->getValue())){
                retval += lhs_->toString() + "⬝" + rhs_->toString() + ".value";
            }
            else{
                retval += lhs_->toString() + "•" + rhs_->toString();
            }
        }
        else{
                retval += lhs_->toString() + "•" + rhs_->toString();
        }

    }

    return retval;
}

bool Interp::hasValue(){
    //auto dc = dynamic_cast<domain::DomainContainer*>(this->domain);
    return this->domain->hasValue();//(dc and dc->hasValue());
};

std::string Interp::getType(){
    if(this->domain->hasValue()){
        //clearly this needs to be changed soon 
        /*
            It would be nice if domain had a ".leanType()" call, but probably not the right thing to do here

            Probably right thing to do is a config to translate a domain type to a lean type/and or constructor function
        */
        //std::cout<<this->domain->getValue()<<"\n";
        if(auto astime = dynamic_cast<domain::Time*>(this->domain->getValue())){
            return std::string("time_expr ") + astime->getSpace()->getName();
        }
        else if(auto asdur = dynamic_cast<domain::Duration*>(this->domain->getValue())){
            return std::string("duration_expr ") + asdur->getSpace()->getName();
        }
        else if(auto astrans = dynamic_cast<domain::TimeTransform*>(this->domain->getValue())){
            auto dom_ = astrans->getDomain();
            auto cod_ = astrans->getCodomain();
            return std::string("time_transform_expr ") + dom_->getName() + " " + cod_->getName(); 
        }
        else if(auto aspos = dynamic_cast<domain::Position*>(this->domain->getValue())){
            return std::string("position_expr ") + aspos->getSpace()->getName();
        }
        else if(auto asdisp = dynamic_cast<domain::Displacement*>(this->domain->getValue())){
            return std::string("displacement_expr ") + asdur->getSpace()->getName();
        }
        else if(auto astrans = dynamic_cast<domain::Geom1DTransform*>(this->domain->getValue())){
            auto dom_ = astrans->getDomain();
            auto cod_ = astrans->getCodomain();
            return std::string("geom1d_transform_expr ") + dom_->getName() + " " + cod_->getName(); 
        }
        else if(auto asscalar = dynamic_cast<domain::Scalar*>(this->domain->getValue())){
            return std::string("scalar_expr");
        }
    }
    else return "_";
};

/*
work in progress


*/
std::string Interp::toStringLinked(std::vector<domain::CoordinateSpace*> spaces){
    std::string retval = "";
    for(auto space:spaces){
        if(auto dc = dynamic_cast<domain::StandardTimeCoordinateSpace*>(space)){
            retval += "def " + space->getName() + "_fr : time_frame_expr := |time_std_frame|\n";
            retval += "def " + space->getName() + " : time_space_expr " + space->getName() + "_fr := |time_std_space|\n\n";
        }
        if(auto dc = dynamic_cast<domain::DerivedTimeCoordinateSpace*>(space)){
            auto parentName = dc->getParent()->getName();
            auto originData = dc->getOrigin();
            auto basisData = dc->getBasis();
            retval += "def " + space->getName() + "_fr : time_frame_expr := \n";
            retval += " let origin := |mk_time " + parentName + ".value " + std::to_string(originData[0]) + "| in\n";
            retval += " let basis := |mk_duration " + parentName + ".value " + std::to_string(basisData[0][0]) + "| in\n";
            retval += " mk_time_frame_expr origin basis\n";
            retval += "def " + space->getName() + " : time_space_expr " + space->getName() + "_fr := mk_time_space_expr " + space->getName() + "_fr\n\n";
        }
        if(auto dc = dynamic_cast<domain::StandardGeom1DCoordinateSpace*>(space)){
            retval += "def " + space->getName() + "_fr : geom1d_frame_expr := |geom1d_std_frame|\n";
            retval += "def " + space->getName() + " : geom1d_space_expr " + space->getName() + "_fr := |geom1d_std_space|\n\n";
        }
        if(auto dc = dynamic_cast<domain::DerivedGeom1DCoordinateSpace*>(space)){
            auto parentName = dc->getParent()->getName();
            auto originData = dc->getOrigin();
            auto basisData = dc->getBasis();
            retval += "def " + space->getName() + "_fr : geom1d_frame_expr := \n";
            retval += " let origin := |mk_position " + parentName + ".value " + std::to_string(originData[0]) + "| in\n";
            retval += " let basis := |mk_displacement " + parentName + ".value " + std::to_string(basisData[0][0]) + "| in\n";
            retval += " mk_geom1d_frame_expr origin basis\n";
            retval += "def " + space->getName() + " : geom1d_space_expr " + space->getName() + "_fr := mk_geom1d_space_expr " + space->getName() + "_fr\n\n";
        }
    }
    //std::cout<<"print nodes\n";
    for(auto op: this->operands){
        retval+= op->toString() + "\n";
        //std::cout<<op->getCoords()->getNodeType()<<"\n";
    }

    return retval;
}

} //namespace interp