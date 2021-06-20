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
    if(nodeType == "COMPOUND_GLOBAL"){
        for(auto op: body){
            retval+= op->toString() + "\n";
        }
    }
    if(nodeType == "FUNCTION_MAIN"){
        
        for(auto op: body){
            retval+= op->toString() + "\n";
        }
    }
    else if (nodeType =="COMPOUND_STMT") {
        for(auto op: body){
            retval+= op->toString() + "\n";
        }
    } 
    else if(nodeType == "DECL_INIT_R1" || nodeType == "DECL_INIT_R3" || nodeType == "DECL_INIT_R4X4") {
        auto var_ = (this->operands[0]);
        auto expr_ = (this->operands[1]);
        retval += std::string("def ") + this->coords->getName() + " : " + (var_->getType()) + " := " + expr_->toString();//[(" +  + ")]";
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
    else if(nodeType == "LIT_R1" || nodeType == "LIT_R3" || nodeType == "LIT_R4X4") {
        
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
            else if(auto aspos = dynamic_cast<domain::Position1D*>(this->domain->getValue())){
                retval+= std::string("mk_position1d ") + aspos->getSpace()->getName() + ".value " + std::to_string(aspos->getValue()[0]);
            }
            else if(auto asdisp = dynamic_cast<domain::Displacement1D*>(this->domain->getValue())){
                retval+= std::string("mk_displacement1d ") + asdisp->getSpace()->getName() + ".value " + std::to_string(asdisp->getValue()[0]);
            }
            else if(auto astrans = dynamic_cast<domain::Geom1DTransform*>(this->domain->getValue())){
                auto dom_ = astrans->getDomain();
                auto cod_ = astrans->getCodomain();
                retval+= dom_->getName() + ".value.mk_geom1d_transform_to " + cod_->getName() + ".value";
            }
            else if(auto aspos = dynamic_cast<domain::Position3D*>(this->domain->getValue())){
                retval+= std::string("mk_position3d ") + aspos->getSpace()->getName() + ".value " + std::to_string(aspos->getValue()[0]) + " " + std::to_string(asdisp->getValue()[1]) + std::to_string(asdisp->getValue()[2]);
            }
            else if(auto asdisp = dynamic_cast<domain::Displacement3D*>(this->domain->getValue())){
                retval+= std::string("mk_displacement3d ") + asdisp->getSpace()->getName() + ".value " + std::to_string(asdisp->getValue()[0]) + " " + std::to_string(asdisp->getValue()[1]) + " " + std::to_string(asdisp->getValue()[2]);
            }
            else if(auto astrans = dynamic_cast<domain::Geom3DTransform*>(this->domain->getValue())){
                auto dom_ = astrans->getDomain();
                auto cod_ = astrans->getCodomain();
                retval+= dom_->getName() + ".value.mk_geom3d_transform_to " + cod_->getName() + ".value";
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
    else if(nodeType == "IDENT_R1" || nodeType == "IDENT_R3" || nodeType == "IDENT_R4X4") {
        retval += this->coords->getName();
    }
    else if(nodeType == "IDENT_LIST_R1" || nodeType == "IDENT_LIST_R3" || nodeType == "IDENT_LIST_R4X4") {
        retval += this->coords->getName();
    }
    else if(nodeType == "REF_R1" || nodeType == "REF_R3" || nodeType == "REF_R4X4") {
        retval += this->coords->getLinked()->getName();
        //if(this->domain->hasValue())
        //    retval += this->domain->getValue()->getName();
    } 
    else if(nodeType == "ADD_R1_R1" || nodeType == "ADD_R3_R3") {
        auto lhs_ = (this->operands[0]);
        auto rhs_ = (this->operands[1]);
        retval += lhs_->toString() + "+ᵥ" + rhs_->toString();
    }
    else if(nodeType == "MUL_R1_R1" || nodeType == "MUL_R1_R3") {
        auto lhs_ = (this->operands[0]);
        auto rhs_ = (this->operands[1]);

        if(lhs_->getDomain()->hasValue()){
            
            if(auto lhstrans = dynamic_cast<domain::CoordinateSpaceTransform*>(lhs_->getDomain()->getValue())){
                if(auto rhstrans = dynamic_cast<domain::CoordinateSpaceTransform*>(rhs_->getDomain()->getValue())){
                    retval += lhs_->toString() + ".value" + "∘" + rhs_->toString() + ".value";
                }
                else
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
    else if(nodeType == "MUL_R4X4_R3"){
        auto lhs_ = (this->operands[0]);
        auto rhs_ = (this->operands[1]);
        retval += lhs_->toString() + "⬝" + rhs_->toString() + ".value";
    }
    else if(nodeType == "MUL_R4X4_R4X4"){
        auto lhs_ = (this->operands[0]);
        auto rhs_ = (this->operands[1]);
        retval += lhs_->toString() + ".value∘" + rhs_->toString() + ".value";
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
        else if(auto aspos = dynamic_cast<domain::Position1D*>(this->domain->getValue())){
            return std::string("position1d_expr ") + aspos->getSpace()->getName();
        }
        else if(auto asdisp = dynamic_cast<domain::Displacement1D*>(this->domain->getValue())){
            return std::string("displacement1d_expr ") + asdisp->getSpace()->getName();
        }
        else if(auto astrans = dynamic_cast<domain::Geom1DTransform*>(this->domain->getValue())){
            auto dom_ = astrans->getDomain();
            auto cod_ = astrans->getCodomain();
            return std::string("geom1d_transform_expr ") + dom_->getName() + " " + cod_->getName(); 
        }
        else if(auto aspos = dynamic_cast<domain::Position3D*>(this->domain->getValue())){
            return std::string("position3d_expr ") + aspos->getSpace()->getName();
        }
        else if(auto asdisp = dynamic_cast<domain::Displacement3D*>(this->domain->getValue())){
            return std::string("displacement3d_expr ") + asdisp->getSpace()->getName();
        }
        else if(auto astrans = dynamic_cast<domain::Geom1DTransform*>(this->domain->getValue())){
            auto dom_ = astrans->getDomain();
            auto cod_ = astrans->getCodomain();
            return std::string("geom1d_transform_expr ") + dom_->getName() + " " + cod_->getName(); 
        }
        else if(auto asscalar = dynamic_cast<domain::Scalar*>(this->domain->getValue())){
            return std::string("scalar_expr");
        }
        else return "_";
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
            retval += " let origin := |mk_position1d " + parentName + ".value " + std::to_string(originData[0]) + "| in\n";
            retval += " let basis := |mk_displacement1d " + parentName + ".value " + std::to_string(basisData[0][0]) + "| in\n";
            retval += " mk_geom1d_frame_expr origin basis\n";
            retval += "def " + space->getName() + " : geom1d_space_expr " + space->getName() + "_fr := mk_geom1d_space_expr " + space->getName() + "_fr\n\n";
        }
        if(auto dc = dynamic_cast<domain::StandardGeom3DCoordinateSpace*>(space)){
            retval += "def " + space->getName() + "_fr : geom3d_frame_expr := |geom3d_std_frame|\n";
            retval += "def " + space->getName() + " : geom3d_space_expr " + space->getName() + "_fr := |geom3d_std_space|\n\n";
        }
        if(auto dc = dynamic_cast<domain::DerivedGeom3DCoordinateSpace*>(space)){
            auto parentName = dc->getParent()->getName();
            auto originData = dc->getOrigin();
            auto basisData = dc->getBasis();
            retval += "def " + space->getName() + "_fr : geom3d_frame_expr := \n";
            retval += " let origin := |mk_position3d " + parentName + ".value " + std::to_string(originData[0])+ " " + std::to_string(originData[1])+ " " + std::to_string(originData[2]) + "| in\n";
            retval += " let basis0 := |mk_displacement3d " + parentName + ".value " + std::to_string(basisData[0][0]) + " " + std::to_string(basisData[0][1]) + " " + std::to_string(basisData[0][2]) + "| in\n";
            retval += " let basis1 := |mk_displacement3d " + parentName + ".value " + std::to_string(basisData[1][0]) + " " + std::to_string(basisData[1][1]) + " " + std::to_string(basisData[1][2]) + "| in\n";
            retval += " let basis2 := |mk_displacement3d " + parentName + ".value " + std::to_string(basisData[2][0]) + " " + std::to_string(basisData[2][1]) + " " + std::to_string(basisData[2][2]) + "| in\n";
            retval += " mk_geom3d_frame_expr origin basis0 basis1 basis2\n";
            retval += "def " + space->getName() + " : geom3d_space_expr " + space->getName() + "_fr := mk_geom3d_space_expr " + space->getName() + "_fr\n\n";
        }
    }
    for(auto op: this->body){
        std::cout<<op->getCoords()->getNodeType()<<"\n";
        retval+= op->toString() + "\n";
    }

    return retval;
}

} //namespace interp