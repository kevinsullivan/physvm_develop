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

OutputState output_state;

//std::shared_ptr<Location> global_loc;

std::string getNextIdentifier(interp::Interp* interp_){

    if(interp_->hasLinked()){
        auto linked = interp_->getLinked();
        if(ident_map.count(linked))
            ident_map[linked]++;
        else
            ident_map[linked] = 0;
        auto coords_ = linked->getCoords();
        return coords_->getName() + std::to_string(ident_map[linked]);
    }
    else{
        if(ident_map.count(interp_))
            ident_map[interp_]++;
        else
            ident_map[interp_] = 0;
        auto coords_ = interp_->getCoords();
        return coords_->getName() + std::to_string(ident_map[interp_]);
    }
}

std::string getLastIdentifier(interp::Interp* interp_){

    if(interp_->hasLinked()){
        auto linked = interp_->getLinked();
        auto coords_ = linked->getCoords();
        if(ident_map.count(linked))
            if(ident_map[linked] == 0)
                return coords_->getName();
            else
                return coords_->getName() + std::to_string(ident_map[linked]);
        else
            return coords_->getName();
    }
    else{
        auto coords_ = interp_->getCoords();
        if(ident_map.count(interp_))
            if(ident_map[interp_] == 0)
                return coords_->getName();
            else
                return coords_->getName() + std::to_string(ident_map[interp_] - 1);
        else
            return coords_->getName();
    }
}

std::string getCurrentIdentifier(interp::Interp* interp_){

    if(interp_->hasLinked()){
        auto linked = interp_->getLinked();
        auto coords_ = linked->getCoords();
        if(ident_map.count(linked))
            return coords_->getName() + std::to_string(ident_map[linked]);
        else
            return coords_->getName();
    }
    else{
        auto coords_ = interp_->getCoords();
        if(ident_map.count(interp_))
            return coords_->getName() + std::to_string(ident_map[interp_]);
        else
            return coords_->getName();
    }
}

//unfortunately I have to do this...arguable architecture limitation of separation of coords,domain,interp
std::string getCurrentIdentifier(domain::DomainObject* domain_){
    for(auto kp : ident_map){
        if(kp.first->getDomain()->getValue() == domain_){
            return getCurrentIdentifier(kp.first);
        }
    }
    return domain_->getName();
}

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
    else if(nodeType == "DECL_INIT_R1" || nodeType == "DECL_INIT_R3" || nodeType == "DECL_INIT_R4X4"  || nodeType == "DECL_INIT_R3X3" || nodeType == "DECL_INIT_R4") {
        auto var_ = (this->operands[0]);
        auto expr_ = (this->operands[1]);
        retval += std::string("def ") + this->coords->getName() + " : " + (var_->getType()) + " := " + expr_->toString();
    }
    else if(nodeType == "DECL_LIST_R1") {
        auto var_ = (this->operands[0]);
        retval += std::string("def ") + getNextIdentifier(var_) + " : list (" + (var_->getType()) + ") := []";
    }
    else if(nodeType == "APPEND_LIST_R1") {
        auto val_ = (this->operands[0]);
        retval += std::string("def ") + getNextIdentifier(this) + " : list (" + (this->getType()) + ") := " + getLastIdentifier(this) + " ++ [" + val_->toString() + "]";
    }
    else if(nodeType == "LIT_R1" || nodeType == "LIT_R3" || nodeType == "LIT_R4X4" || nodeType == "LIT_R4" || nodeType == "LIT_R3X3") {
        
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
                retval+= std::string("mk_position3d ") + aspos->getSpace()->getName() + ".value " + std::to_string(aspos->getValue()[0]) + " " + std::to_string(aspos->getValue()[1]) + " " + std::to_string(aspos->getValue()[2]);
            }
            else if(auto asdisp = dynamic_cast<domain::Displacement3D*>(this->domain->getValue())){
                retval+= std::string("mk_displacement3d ") + asdisp->getSpace()->getName() + ".value " + std::to_string(asdisp->getValue()[0]) + " " + std::to_string(asdisp->getValue()[1]) + " " + std::to_string(asdisp->getValue()[2]);
            }
            else if(auto asort = dynamic_cast<domain::Orientation3D*>(this->domain->getValue())){
                if(nodeType != "LIT_R4"){
                retval+= std::string("mk_orientation3d ") + asort->getSpace()->getName() + ".value "
                     + std::to_string(asort->getValue()[0]) + " " + std::to_string(asort->getValue()[1]) + " " + std::to_string(asort->getValue()[2]) + " " 
                     + std::to_string(asort->getValue()[3]) + " " + std::to_string(asort->getValue()[4]) + " " + std::to_string(asort->getValue()[5]) + " " 
                     + std::to_string(asort->getValue()[6]) + " " + std::to_string(asort->getValue()[7]) + " " + std::to_string(asort->getValue()[8]);
                }
                else{
                    retval+= std::string("mk_orientation3d_from_quaternion ") + asort->getSpace()->getName() + ".value "
                        + std::to_string(asort->getValue()[0]) + " " + std::to_string(asort->getValue()[1]) + " " + std::to_string(asort->getValue()[2]) + " " 
                        + std::to_string(asort->getValue()[3]);
                }
            }
            else if(auto asrot = dynamic_cast<domain::Rotation3D*>(this->domain->getValue())){
                if(nodeType != "LIT_R4"){
                    retval+= std::string("mk_rotation3d ") + asrot->getSpace()->getName() + ".value "
                        + std::to_string(asrot->getValue()[0]) + " " + std::to_string(asrot->getValue()[1]) + " " + std::to_string(asrot->getValue()[2]) + " " 
                        + std::to_string(asrot->getValue()[3]) + " " + std::to_string(asrot->getValue()[4]) + " " + std::to_string(asrot->getValue()[5]) + " " 
                        + std::to_string(asrot->getValue()[6]) + " " + std::to_string(asrot->getValue()[7]) + " " + std::to_string(asrot->getValue()[8]);
                }
                else{
                    retval+= std::string("mk_rotation3d_from_quaternion ") + asrot->getSpace()->getName() + ".value "
                        + std::to_string(asrot->getValue()[0]) + " " + std::to_string(asrot->getValue()[1]) + " " + std::to_string(asrot->getValue()[2]) + " " 
                        + std::to_string(asrot->getValue()[3]);
                }
            }
            else if(auto aspose = dynamic_cast<domain::Pose3D*>(this->domain->getValue())){
                auto ort = aspose->getOrientation();
                auto pos = aspose->getPosition();
                retval+= std::string("mk_pose3d ") + aspose->getSpace()->getName() + ".value " ;
                retval+= std::string("\n\t\t(mk_orientation3d ") + ort->getSpace()->getName() + ".value "
                     + std::to_string(ort->getValue()[0]) + " " + std::to_string(ort->getValue()[1]) + " " + std::to_string(ort->getValue()[2]) + " " 
                     + std::to_string(ort->getValue()[3]) + " " + std::to_string(ort->getValue()[4]) + " " + std::to_string(ort->getValue()[5]) + " "
                     + std::to_string(ort->getValue()[6]) + " " + std::to_string(ort->getValue()[7]) + " " + std::to_string(ort->getValue()[8]) + ")";
                retval+= std::string("\n\t\t(mk_position3d ") + pos->getSpace()->getName() + ".value " + std::to_string(pos->getValue()[0]) + " " + std::to_string(pos->getValue()[1]) + " " + std::to_string(pos->getValue()[2]) + ")";
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
    else if(nodeType == "IDENT_R1" || nodeType == "IDENT_R3" || nodeType == "IDENT_R4X4" || nodeType == "IDENT_R4" || nodeType == "IDENT_R3X3") {
        retval += this->coords->getName();
    }
    else if(nodeType == "IDENT_LIST_R1" || nodeType == "IDENT_LIST_R3" || nodeType == "IDENT_LIST_R4X4") {
        retval += this->coords->getName();
    }
    else if(nodeType == "REF_R1" || nodeType == "REF_R4X4") {
        retval += this->coords->getLinked()->getName();
    } 
    else if(nodeType == "REF_R3"){
        if(this->hasContainer()){
            auto container = this->getContainer();
            if(auto aspose = dynamic_cast<domain::Pose3D*>(container->getDomain()->getValue())){
                retval += container->getCoords()->getName() + ".position";
            }
            else{
                retval += container->getCoords()->getName() + ".property";
            }
        }
        else
            retval += this->coords->getLinked()->getName();
    }
    else if(nodeType == "REF_R4" || nodeType =="REF_R3X3"){
        
        if(this->getCoords()->hasContainer()){
            auto container = this->getCoords()->getContainer();
            if(auto aspose = dynamic_cast<domain::Pose3D*>(container)){
                retval += container->getName() + ".orientation";
            }
            else{
                retval += container->getName() + ".property";

            }
        }
        else
            retval += this->coords->getLinked()->getName();
    }
    else if(nodeType == "ADD_R1_R1" || nodeType == "ADD_R3_R3") {
        auto lhs_ = (this->operands[0]);
        auto rhs_ = (this->operands[1]);
        retval += lhs_->toString() + "+ᵥ" + rhs_->toString();
    }
    else if(nodeType == "SUB_R1_R1" || nodeType == "SUB_R3_R3") {
        auto lhs_ = (this->operands[0]);
        auto rhs_ = (this->operands[1]);
        retval += lhs_->toString() + "-ᵥ" + rhs_->toString();
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
    else if(nodeType.find("INV") != string::npos){
        retval += "(("+this->operands[0]->toString()+")⁻¹)";
    }
    else if(nodeType=="ASSIGN_MUL_R4X4_R4X4"){
        auto member = this->operands[0]->getLinked();
        auto lhs_ = this->operands[1];
        auto rhs_ = this->operands[2];

        retval += std::string("def ") + getNextIdentifier(member) + " : " + (member->getType()) + " := " + lhs_->toString() + ".value∘" + rhs_->toString() + ".value";;
    }
    else if(nodeType=="ASSIGN_R3X3" || nodeType=="ASSIGN_R4"){


        if(this->operands[0]->hasContainer()){
            auto container = this->operands[0]->getContainer();
            if(auto aspose = dynamic_cast<domain::Pose3D*>(container->getDomain()->getValue())){
                retval += container->getCoords()->getName() + ".orientation";
            }
            else{
                retval += container->getCoords()->getName() + ".property";

            }
        }
        else {
            auto member = this->operands[0]->getLinked();
            auto val = this->operands[1];

            retval += std::string("def ") + getNextIdentifier(member) + " : " + (member->getType()) + " := " + val->toString();
        }
    }
    //this doesn't belong here, but deadlines!
    else if(nodeType=="ASSIGN_R3X3_SWAP" || nodeType=="ASSIGN_R4_SWAP"){//pose value is on the right, assign to orientation on left
        auto lhs = this->operands[1];
        auto rhs = this->operands[0];
        if(lhs->hasContainer() and rhs->hasContainer()){
            throw "Not implemented";
        }
        else if (lhs->hasContainer()){
        }
        else if(rhs->hasContainer()){
            auto member = lhs->getLinked();

            retval += std::string("def ") + getNextIdentifier(member) + " : " + (member->getType()) + " := ";
            auto container = rhs->getContainer();
            auto old_ident = ident_map.count(container) 
                ? container->getCoords()->getName() + std::to_string((ident_map[container])) 
                : container->getCoords()->getName();
        
            if(auto aspose = dynamic_cast<domain::Pose3D*>(container->getDomain()->getValue())){
                retval += "|" + old_ident + ".value.orientation|";
            }
            else {
                retval += "|" + old_ident + ".value.property|";
            }
        }
        else {
            auto member = this->operands[0]->getLinked();
            auto val = this->operands[1];

            retval += std::string("def ") + getNextIdentifier(member) + " : " + (member->getType()) + " := " + val->toString();
        }
    }
    else if(nodeType=="ASSIGN_R4X4_AT_R3"){
        auto member = this->operands[0]->getLinked();//->getContainer();

        auto old_name = ident_map.count(member) ? member->getCoords()->getName() + std::to_string((ident_map[member])) : member->getCoords()->getName();
        
        auto val = this->operands[1];


        if(auto pose = dynamic_cast<domain::Pose3D*>(member->getDomain()->getValue())){
            retval += std::string("def ") + getNextIdentifier(member)
                + " : " + (member->getType()) + " := |{\n\t\tposition:=(" + val->toString() + ").value,\n\t\t.."+old_name+".value\n}|";

        }
        else{
            retval += std::string("def ") + getNextIdentifier(member)
                + " : " + (member->getType()) + " := |{\n\t\t.."+old_name+"\n}|";

        }

    }
    else if(nodeType=="ASSIGN_R4X4_AT_R3X3" || nodeType == "ASSIGN_R4X4_AT_R4"){
        auto member = this->operands[0]->getLinked();
        auto old_name = ident_map.count(member) ? member->getCoords()->getName() + std::to_string((ident_map[member])) : member->getCoords()->getName();

        auto val = this->operands[1];
        if(auto pose = dynamic_cast<domain::Pose3D*>(member->getDomain()->getValue())){
            retval += std::string("def ") + getNextIdentifier(member)
                + " : " + (member->getType()) + " := |{\n\t\torientation:=("  + val->toString() + ").value,\n\t\t.."+old_name+".value\n}|";

        }
        else{
            retval += std::string("def ") + getNextIdentifier(member)
                + " : " + (member->getType()) + " := |{\n\t\t.."+old_name+"\n}|";

        }
    }



    return retval;
}

void Interp::buildString(bool withType){
    std::string nodeType = this->coords->getNodeType();
    auto begin = output_state.getCurrentLoc();
    if(nodeType == "COMPOUND_GLOBAL"){
        for(auto op: body){
            op->setStartLocation(output_state.getCurrentLoc());
            op->buildString();
            op->setEndLocation(output_state.getCurrentLoc());
            output_state.update("\n");
        }
    }
    if(nodeType == "FUNCTION_MAIN"){
        
        for(auto op: body){
            op->setStartLocation(output_state.getCurrentLoc());
            op->buildString();
            op->setEndLocation(output_state.getCurrentLoc());
            output_state.update("\n");

        }
    }
    else if (nodeType =="COMPOUND_STMT") {
        for(auto op: body){
            op->setStartLocation(output_state.getCurrentLoc());
            op->buildString();
            //output_state.update( op->toString() + "\n");
            op->setEndLocation(output_state.getCurrentLoc());
            output_state.update("\n");
        }
    } 
    else if(nodeType == "DECL_INIT_BOOL"){
        auto var_ = (this->operands[0]);
        auto expr_ = (this->operands[1]);
        output_state.update("def ");
        var_->buildString(); 
        output_state.update(" := \n\t\t");
        expr_->buildString();
        if(var_->hasValue()){
            output_state.update("\n");
            if(auto bt = dynamic_cast<domain::BoolTrue*>(var_->getValue())){
                output_state.update(std::string("def ") + var_->getCoords()->getName() + ".sem : bool_sem " + var_->getCoords()->getName());
                output_state.update(" := ");
                output_state.update(" bool_sem.bool_eval_true _ begin check_bool_true hasRecentTargetPose end\n");
            }
            else if(auto bt = dynamic_cast<domain::BoolFalse*>(var_->getValue())){
                output_state.update(std::string("def ") + var_->getCoords()->getName() + ".sem : bool_sem " + var_->getCoords()->getName());
                output_state.update(" := ");
                output_state.update(" bool_sem.bool_eval_false _ begin check_bool_false hasRecentTargetPose end\n");
            }
        }

        //std::cout<<expr_->getCoords()->getNodeType()<<"\n";
    }
    else if(nodeType == "DECL_INIT_R1" || nodeType == "DECL_INIT_R3" || nodeType == "DECL_INIT_R4X4"  || nodeType == "DECL_INIT_R3X3" || nodeType == "DECL_INIT_R4") {
            
        auto var_ = (this->operands[0]);
        auto expr_ = (this->operands[1]);

        if(auto dc = dynamic_cast<domain::TimeSeries*>(var_->getDomain()->getValue())){
            
        /*
            if its a time series IDENT, don't print it off, it's already been hoisted to the top
            if it's a time series LIT, CHECK if the lit is timestamped
            if it's timestamped, print off the timestamped
            if not, print off _->LIT
            change interp's loc to range of inner expression
        */
            output_state.update(std::string("def ") + getNextIdentifier(var_) + ":=" + getLastIdentifier(var_));
            //output_state.update(std::string("["));
            if(expr_->hasValue()){
                output_state.update(std::string("["));
                auto exprbegin = output_state.getCurrentLoc();
                if(auto dci = dynamic_cast<domain::TimeStamped*>(expr_->getDomain()->getValue())){
                    output_state.update("((|");
                    auto astime = dci->getTime();
                    output_state.update( std::string("mk_time ") + astime->getSpace()->getName() + ".value " + std::to_string(astime->getValue()[0]));
                    auto exprbegin = output_state.getCurrentLoc();
                    output_state.update("|↦|");
                    if(auto astspose = dynamic_cast<domain::TimeStampedPose3D*>(dci)){
                        auto aspose = astspose->getValue();
                        auto ort = aspose->getOrientation();
                        auto pos = aspose->getPosition();
                        output_state.update( std::string("mk_pose3d ") + aspose->getSpace()->getName() + ".value ");
                        output_state.update( std::string("\n\t\t(mk_orientation3d ") + ort->getSpace()->getName() + ".value "
                            + std::to_string(ort->getValue()[0]) + " " + std::to_string(ort->getValue()[1]) + " " + std::to_string(ort->getValue()[2]) + " " 
                            + std::to_string(ort->getValue()[3]) + " " + std::to_string(ort->getValue()[4]) + " " + std::to_string(ort->getValue()[5]) + " "
                            + std::to_string(ort->getValue()[6]) + " " + std::to_string(ort->getValue()[7]) + " " + std::to_string(ort->getValue()[8]) + ")");
                        output_state.update( std::string("\n\t\t(mk_position3d ") + pos->getSpace()->getName() + ".value " + std::to_string(pos->getValue()[0]) + " " + std::to_string(pos->getValue()[1]) + " " + std::to_string(pos->getValue()[2]) + ")");
                    }
                    else if(auto aststrans = dynamic_cast<domain::TimeStampedGeom3DTransform*>(dci)){
                        auto astrans = aststrans->getValue();
                        auto dom_ = astrans->getDomain();
                        auto cod_ = astrans->getCodomain();
                        output_state.update( dom_->getName() + ".value.mk_geom3d_transform_to " + cod_->getName() + ".value");
                    }
                    else{
                        output_state.update("_");
                    }
                    
                    output_state.update("|:_))");
                }
                else{
                    output_state.update("((_↦");
                    expr_->buildString();
                    output_state.update(":_))");
                }
                expr_->setStartLocation(exprbegin);
                expr_->setEndLocation(output_state.getCurrentLoc());
                output_state.update(std::string("]"));
            }
            else {
               // output_state.update("((_:_))");
               expr_->setStartLocation(output_state.getCurrentLoc());
               expr_->setEndLocation(output_state.getCurrentLoc());
            }
            //output_state.update(std::string("]"));

        }
        else{
            output_state.update( std::string("def ") );
            var_->buildString(); 
            output_state.update(" := "); 
            expr_->buildString();
        }
    }
    else if(nodeType == "DECL_LIST_R1") {
        auto var_ = (this->operands[0]);
        output_state.update( std::string("def "));
        var_->buildString();
        output_state.update(std::string("") + " : list (" + (var_->getType()) + ") := []");
    }
    else if(nodeType == "APPEND_LIST_R1") {
        auto val_ = (this->operands[0]);
        output_state.update( 
            std::string("def ") + getNextIdentifier(this) + " : list (" + (this->getType()) + 
            ") := " + getLastIdentifier(this) + " ++ ["); 
        val_->buildString();
        output_state.update(std::string("]"));
    }
    else if(nodeType == "LIT_R1" || nodeType == "LIT_R3" 
        || nodeType == "LIT_R4X4" || nodeType == "LIT_R4" 
        || nodeType == "LIT_R3X3") {
        
        output_state.update("((");

        if(this->constructor and this->constructor->hasValue()){
            output_state.update( "(");
        }

        if(this->domain->hasValue()){
            /*
                Move this into config as well
            */


            output_state.update( "|");
            if(auto astime = dynamic_cast<domain::Time*>(this->domain->getValue())){
                output_state.update( std::string("mk_time ") + astime->getSpace()->getName() + ".value " + std::to_string(astime->getValue()[0]));
            }
            else if(auto asdur = dynamic_cast<domain::Duration*>(this->domain->getValue())){
                output_state.update( std::string("mk_duration ") + asdur->getSpace()->getName() + ".value " + std::to_string(asdur->getValue()[0]));
            }
            else if(auto asscalar = dynamic_cast<domain::Scalar*>(this->domain->getValue())){
                output_state.update( std::string("(") + std::to_string(asscalar->getValue()[0]) + " : scalar)");
            }
            else if(auto astrans = dynamic_cast<domain::TimeTransform*>(this->domain->getValue())){
                auto dom_ = astrans->getDomain();
                auto cod_ = astrans->getCodomain();
                output_state.update( dom_->getName() + ".value.mk_time_transform_to " + cod_->getName() + ".value");
            }
            else if(auto aspos = dynamic_cast<domain::Position1D*>(this->domain->getValue())){
                output_state.update( std::string("mk_position1d ") + aspos->getSpace()->getName() + ".value " + std::to_string(aspos->getValue()[0]));
            }
            else if(auto asdisp = dynamic_cast<domain::Displacement1D*>(this->domain->getValue())){
                output_state.update( std::string("mk_displacement1d ") + asdisp->getSpace()->getName() + ".value " + std::to_string(asdisp->getValue()[0]));
            }
            else if(auto astrans = dynamic_cast<domain::Geom1DTransform*>(this->domain->getValue())){
                auto dom_ = astrans->getDomain();
                auto cod_ = astrans->getCodomain();
                output_state.update( dom_->getName() + ".value.mk_geom1d_transform_to " + cod_->getName() + ".value");
            }
            else if(auto aspos = dynamic_cast<domain::Position3D*>(this->domain->getValue())){
                output_state.update( std::string("mk_position3d ") + aspos->getSpace()->getName() + ".value " + std::to_string(aspos->getValue()[0]) + " " + std::to_string(aspos->getValue()[1]) + " " + std::to_string(aspos->getValue()[2]));
            }
            else if(auto asdisp = dynamic_cast<domain::Displacement3D*>(this->domain->getValue())){
                output_state.update( std::string("mk_displacement3d ") + asdisp->getSpace()->getName() + ".value " + std::to_string(asdisp->getValue()[0]) + " " + std::to_string(asdisp->getValue()[1]) + " " + std::to_string(asdisp->getValue()[2]));
            }
            else if(auto asort = dynamic_cast<domain::Orientation3D*>(this->domain->getValue())){
                if(nodeType != "LIT_R4"){
                output_state.update( std::string("mk_orientation3d ") + asort->getSpace()->getName() + ".value "
                     + std::to_string(asort->getValue()[0]) + " " + std::to_string(asort->getValue()[1]) + " " + std::to_string(asort->getValue()[2]) + " " 
                     + std::to_string(asort->getValue()[3]) + " " + std::to_string(asort->getValue()[4]) + " " + std::to_string(asort->getValue()[5]) + " " 
                     + std::to_string(asort->getValue()[6]) + " " + std::to_string(asort->getValue()[7]) + " " + std::to_string(asort->getValue()[8]));
                }
                else{
                    output_state.update( std::string("mk_orientation3d_from_quaternion ") + asort->getSpace()->getName() + ".value "
                        + std::to_string(asort->getValue()[0]) + " " + std::to_string(asort->getValue()[1]) + " " + std::to_string(asort->getValue()[2]) + " " 
                        + std::to_string(asort->getValue()[3]));
                }
            }
            else if(auto asrot = dynamic_cast<domain::Rotation3D*>(this->domain->getValue())){
                if(nodeType != "LIT_R4"){
                    output_state.update( std::string("mk_rotation3d ") + asrot->getSpace()->getName() + ".value "
                        + std::to_string(asrot->getValue()[0]) + " " + std::to_string(asrot->getValue()[1]) + " " + std::to_string(asrot->getValue()[2]) + " " 
                        + std::to_string(asrot->getValue()[3]) + " " + std::to_string(asrot->getValue()[4]) + " " + std::to_string(asrot->getValue()[5]) + " " 
                        + std::to_string(asrot->getValue()[6]) + " " + std::to_string(asrot->getValue()[7]) + " " + std::to_string(asrot->getValue()[8]));
                }
                else{
                    output_state.update( std::string("mk_rotation3d_from_quaternion ") + asrot->getSpace()->getName() + ".value "
                        + std::to_string(asrot->getValue()[0]) + " " + std::to_string(asrot->getValue()[1]) + " " + std::to_string(asrot->getValue()[2]) + " " 
                        + std::to_string(asrot->getValue()[3]));
                }
            }
            else if(auto aspose = dynamic_cast<domain::Pose3D*>(this->domain->getValue())){
                auto ort = aspose->getOrientation();
                auto pos = aspose->getPosition();
                output_state.update( std::string("mk_pose3d ") + aspose->getSpace()->getName() + ".value ");
                output_state.update( std::string("\n\t\t(mk_orientation3d ") + ort->getSpace()->getName() + ".value "
                     + std::to_string(ort->getValue()[0]) + " " + std::to_string(ort->getValue()[1]) + " " + std::to_string(ort->getValue()[2]) + " " 
                     + std::to_string(ort->getValue()[3]) + " " + std::to_string(ort->getValue()[4]) + " " + std::to_string(ort->getValue()[5]) + " "
                     + std::to_string(ort->getValue()[6]) + " " + std::to_string(ort->getValue()[7]) + " " + std::to_string(ort->getValue()[8]) + ")");
                output_state.update( std::string("\n\t\t(mk_position3d ") + pos->getSpace()->getName() + ".value " + std::to_string(pos->getValue()[0]) + " " + std::to_string(pos->getValue()[1]) + " " + std::to_string(pos->getValue()[2]) + ")");
            }
            else if(auto astrans = dynamic_cast<domain::Geom3DTransform*>(this->domain->getValue())){
                auto dom_ = astrans->getDomain();
                auto cod_ = astrans->getCodomain();
                output_state.update( dom_->getName() + ".value.mk_geom3d_transform_to " + cod_->getName() + ".value");
            }
            else if(auto astspose = dynamic_cast<domain::TimeStampedPose3D*>(this->domain->getValue())){
                auto astime = astspose->getTime();
                output_state.update( std::string("mk_time ") + astime->getSpace()->getName() + ".value " + std::to_string(astime->getValue()[0]));
                output_state.update(",");
                auto aspose = astspose->getValue();
                auto ort = aspose->getOrientation();
                auto pos = aspose->getPosition();
                output_state.update( std::string("mk_pose3d ") + aspose->getSpace()->getName() + ".value ");
                output_state.update( std::string("\n\t\t(mk_orientation3d ") + ort->getSpace()->getName() + ".value "
                    + std::to_string(ort->getValue()[0]) + " " + std::to_string(ort->getValue()[1]) + " " + std::to_string(ort->getValue()[2]) + " " 
                    + std::to_string(ort->getValue()[3]) + " " + std::to_string(ort->getValue()[4]) + " " + std::to_string(ort->getValue()[5]) + " "
                    + std::to_string(ort->getValue()[6]) + " " + std::to_string(ort->getValue()[7]) + " " + std::to_string(ort->getValue()[8]) + ")");
                output_state.update( std::string("\n\t\t(mk_position3d ") + pos->getSpace()->getName() + ".value " + std::to_string(pos->getValue()[0]) + " " + std::to_string(pos->getValue()[1]) + " " + std::to_string(pos->getValue()[2]) + ")");
            }
            else if(auto aststrans = dynamic_cast<domain::TimeStampedGeom3DTransform*>(this->domain->getValue())){
                auto astime = aststrans->getTime();
                output_state.update( std::string("mk_time ") + astime->getSpace()->getName() + ".value " + std::to_string(astime->getValue()[0]));
                output_state.update(",");
                auto astrans = aststrans->getValue();
                auto dom_ = astrans->getDomain();
                auto cod_ = astrans->getCodomain();
                output_state.update( dom_->getName() + ".value.mk_geom3d_transform_to " + cod_->getName() + ".value");
            }
            else if (auto as_si = dynamic_cast<domain::SeriesIndex*>(this->domain->getValue())){
                if(as_si->getLatest()){
                    output_state.update(getCurrentIdentifier(as_si->getSeries())+ ".value.latest" );
                }
                else{
                    output_state.update(getCurrentIdentifier(as_si->getSeries()) + ".value.sample ");
                    output_state.update(std::string("(mk_time _") + std::to_string(as_si->getTime()->getValue()[0]) +")");
                }
            }
            else output_state.update("_");
            output_state.update( "|");

        }
        else{
            output_state.update( "_");
        }
        
        if(this->constructor and this->constructor->hasValue()){
            output_state.update( " : " + this->constructor->getType() + ")");
        }

        output_state.update(":" + this->getType()+"))");
    } 
    else if(nodeType == "IDENT_R1" || nodeType == "IDENT_R3" 
    || nodeType == "IDENT_R4X4" || nodeType == "IDENT_R4" 
    || nodeType == "IDENT_R3X3") {
        if(!withType)
            output_state.update( this->coords->getName());
        else{
            output_state.update( this->coords->getName() + " : " + this->getType());
            //this->setStartLocation(begin);
            //this->setEndLocation(end);
        }

    }
    else if(nodeType == "IDENT_BOOL"){
        if(!withType)
            output_state.update( this->coords->getName());
        else{
            output_state.update( this->coords->getName() + " : bool_expr");
            //this->setStartLocation(begin);
            //this->setEndLocation(end);
        }

    }
    else if(nodeType == "IDENT_LIST_R1" || nodeType == "IDENT_LIST_R3" || nodeType == "IDENT_LIST_R4X4") {
        if(!withType)
            output_state.update( this->coords->getName());
        else{
            output_state.update( this->coords->getName() + " : " + this->getType());
        }
    }
    else if(nodeType == "REF_R1" || nodeType == "REF_R4X4") {
        /*if(auto dcts = dynamic_cast<domain::TimeSeries*>(this->getLinked()->getDomain()->getValue())){
            if(!withType)
                output_state.update(getLastIdentifier(this->getLinked())+".");
            else
                output_state.update("(("+ this->coords->getLinked()->getName() 
                    + " : " + this->getLinked()->getType()+"))");
        }*/
        if(0){}
        else if(this->hasContainer()){
            auto isTimestamped = dynamic_cast<domain::TimeStamped*>(this->getContainer()->getDomain()->getValue());
            auto isTimeSeries = dynamic_cast<domain::TimeSeries*>(this->getContainer()->getDomain()->getValue());
            if(!withType)
                output_state.update(getCurrentIdentifier(this->getContainer()));
            else
                if(isTimestamped)
                    output_state.update("((|"+ getCurrentIdentifier(this->getContainer()) 
                        + ".value.timestamp| : _))");
                else if(isTimeSeries)
                    output_state.update("((|"+ getCurrentIdentifier(this->getContainer()) 
                        + ".value.latest.timestamp| : _))");
                else
                    output_state.update("((|"+ getCurrentIdentifier(this->getContainer()) 
                        + ".value.property| : _))");
        }
        else{
            if(!withType)
                output_state.update(getCurrentIdentifier(this));
            else
                output_state.update("(("+ getCurrentIdentifier(this) 
                    + " : " + this->getLinked()->getType()+"))");

        }
    } 
    else if(nodeType == "REF_R3"){
        if(this->hasContainer()){
            output_state.update("((");
            auto container = this->getContainer();
            if(auto aspose = dynamic_cast<domain::Pose3D*>(container->getDomain()->getValue())){
                output_state.update(container->getCoords()->getName() + ".position");
            }
            else{
                output_state.update(container->getCoords()->getName() + ".property");
            }
            output_state.update(":_))");
        }
        else{
            if(!withType)
                output_state.update(this->coords->getLinked()->getName());
            else{
                output_state.update("((");
                output_state.update(this->coords->getLinked()->getName());
                output_state.update(":"+this->getLinked()->getType()+"))");
            }
        }
    }
    else if(nodeType == "REF_R4" || nodeType =="REF_R3X3"){
        if(this->getCoords()->hasContainer()){
            auto container = this->getCoords()->getContainer();
            if(auto aspose = dynamic_cast<domain::Pose3D*>(container)){
                output_state.update("((");
                output_state.update(container->getName() + ".orientation");
                output_state.update(":_))");
            }
            else{
                output_state.update("((");
                output_state.update( container->getName() + ".property");
                output_state.update(":_))");
            }
        }
        else{
            if(!withType)
                output_state.update(this->coords->getLinked()->getName());
            else{
                output_state.update("((");
                output_state.update(this->coords->getLinked()->getName());
                output_state.update(":" +this->getLinked()->getType() +"))");
            }
        }
    }
    else if(nodeType == "ADD_R1_R1" || nodeType == "ADD_R3_R3") {
        auto lhs_ = (this->operands[0]);
        auto rhs_ = (this->operands[1]);
        output_state.update("((");
        lhs_->buildString();
        output_state.update("+ᵥ");
        rhs_->buildString();
        output_state.update(":" +this->getType() +"))");
    }
    else if(nodeType == "SUB_R1_R1" || nodeType == "SUB_R3_R3") {
        auto lhs_ = (this->operands[0]);
        auto rhs_ = (this->operands[1]);
        output_state.update("((");
        lhs_->buildString();
        output_state.update("-ᵥ");
        rhs_->buildString();
        output_state.update(":" +this->getType() +"))");
    }
    else if(nodeType == "MUL_R1_R1" || nodeType == "MUL_R1_R3") {
        auto lhs_ = (this->operands[0]);
        auto rhs_ = (this->operands[1]);
        output_state.update("((");

        if(lhs_->getDomain()->hasValue()){
            
            if(auto lhstrans = dynamic_cast<domain::CoordinateSpaceTransform*>(lhs_->getDomain()->getValue())){
                if(auto rhstrans = dynamic_cast<domain::CoordinateSpaceTransform*>(rhs_->getDomain()->getValue())){
                    lhs_->buildString();
                    output_state.update(".value");
                    output_state.update("∘");
                    rhs_->buildString();
                    output_state.update(".value");
                }
                else {
                    lhs_->buildString();
                    output_state.update("⬝");
                    rhs_->buildString();
                    output_state.update(".value");
                }
            }
            else{
                lhs_->buildString();
                output_state.update("•");
                rhs_->buildString();
            }
        }
        else{
                lhs_->buildString();
                output_state.update("•");
                rhs_->buildString();
        }
        output_state.update(":" +this->getType() +"))");
    }
    else if(nodeType == "MUL_R4X4_R3"){
        auto lhs_ = (this->operands[0]);
        auto rhs_ = (this->operands[1]);
        output_state.update("((");
        lhs_->buildString();
        output_state.update("⬝");
        rhs_->buildString();
        output_state.update(".value");
        output_state.update(":" +this->getType() +"))");
    }
    else if(nodeType == "MUL_R4X4_R4X4"){
        auto lhs_ = (this->operands[0]);
        auto rhs_ = (this->operands[1]);
        output_state.update("((");
        lhs_->buildString();
        output_state.update(".value");
        output_state.update("∘");
        rhs_->buildString();
        output_state.update(".value");
        output_state.update(":" +this->getType() +"))");
    }
    else if(nodeType.find("INV") != string::npos){
        output_state.update( "((");
        this->operands[0]->buildString();
        output_state.update("⁻¹:" +this->getType() +"))");
    }
    else if(nodeType.find("ASSIGN_MUL_R4X4_R4X4") != string::npos){
        auto member_ = this->operands[0]->getLinked();
        auto lhs_ = this->operands[1];
        auto rhs_ = this->operands[2];

        if(nodeType=="ASSIGN_MUL_R4X4_R4X4_2"){//OKAY, THIS LOGIC REALLY NEEDS TO GET PUSHED TO GEN
            rhs_ = this->operands[0];//timestamped series ... assume latest
            member_ = this->operands[1]->getLinked();//check if member is a timestamped series, if so, different logic
            lhs_ = this->operands[2];//check if lhs is timestamped, if so, get the value
        }

        
        if(auto dc = dynamic_cast<domain::TimeSeries*>(member_->getDomain()->getValue())){
            
        /*
            check if the lhs is a timestamped transform
            if it is print off t
            if it is not, print off an empty time plus the literal expression

        */
            output_state.update(std::string("def ") + getNextIdentifier(member_) + ":=" + getLastIdentifier(member_));
            output_state.update(std::string("[("));
            if(lhs_->hasValue()){
                if(auto dci = dynamic_cast<domain::TimeStampedGeom3DTransform*>(lhs_->getValue())){
                    output_state.update("|(");
                    output_state.update(getCurrentIdentifier(lhs_));
                    output_state.update(".value.timestamp)|");
                    output_state.update("↦|(");
                    output_state.update(getCurrentIdentifier(lhs_));
                    output_state.update(".value.value");
                    output_state.update("⬝");
                    if(auto dci = dynamic_cast<domain::Pose3DSeries*>(rhs_->getValue())){
                        output_state.update(getCurrentIdentifier(rhs_) + ".value.latest.value");
                    }
                    else{
                        output_state.update(std::string("("));
                        rhs_->buildString();
                        output_state.update(std::string(").value"));
                    }

                    output_state.update(")|");
                }
                else{
                    output_state.update("|(");
                    output_state.update("mk_time _ _");
                    output_state.update(")|");
                    output_state.update("↦|((");
                    lhs_->buildString();
                    output_state.update(".value)⬝");
                    if(auto dci = dynamic_cast<domain::Pose3DSeries*>(rhs_->getValue())){
                        output_state.update(getCurrentIdentifier(rhs_) + ".value.value");
                    }
                    else{
                        output_state.update(std::string("("));
                        rhs_->buildString();
                        output_state.update(std::string(").value"));
                    }

                    output_state.update(")|");
                }
            }
            else {
                output_state.update("((_:_))");
            }
            output_state.update(std::string(")]"));

        }
        else{
            output_state.update( std::string("def "));
            //member->buildString(false);
            output_state.update(getNextIdentifier(member_) + " : " + (member_->getType()) + " := "); 
            lhs_->buildString();
            output_state.update(".value");
            output_state.update("∘");
            rhs_->buildString();
            output_state.update(".value");
        }
    }
    else if(nodeType=="ASSIGN_R3X3" || nodeType=="ASSIGN_R4"){


        if(this->operands[0]->hasContainer()){
            auto container = this->operands[0]->getContainer();
            if(auto aspose = dynamic_cast<domain::Pose3D*>(container->getDomain()->getValue())){
                output_state.update( container->getCoords()->getName() + ".orientation");
            }
            else{
                output_state.update( container->getCoords()->getName() + ".property");

            }
        }
        else {
            auto member = this->operands[0]->getLinked();
            //auto iident_ = ident_map.count(member) ? (ident_map[member] = ++ident_map[member]) : (ident_map[member] = ident_++);
            auto val = this->operands[1];

            output_state.update( std::string("def "));
            //member->buildString(false);
            output_state.update(getNextIdentifier(member) + " : " + (member->getType()) + " := "); 
            val->buildString();
        }
    }
    //this doesn't belong here, but deadlines!
    else if(nodeType=="ASSIGN_R3X3_SWAP" || nodeType=="ASSIGN_R4_SWAP"){//pose value is on the right, assign to orientation on left
        auto lhs = this->operands[1];
        auto rhs = this->operands[0];
        if(lhs->hasContainer() and rhs->hasContainer()){
            throw "Not implemented";
        }
        else if (lhs->hasContainer()){
        }
        else if(rhs->hasContainer()){
            auto member = lhs->getLinked();
            //auto iident_ = ident_map.count(member) ? (ident_map[member] = ++ident_map[member]) : (ident_map[member] = ident_++);

            output_state.update( std::string("def "));
            //member->buildString(false);
            output_state.update(getNextIdentifier(member) + " : " + (member->getType()) + " := ");
            auto container = rhs->getContainer();
            auto old_ident = ident_map.count(container) 
                ? container->getCoords()->getName() + std::to_string((ident_map[container])) 
                : container->getCoords()->getName();
        
            if(auto aspose = dynamic_cast<domain::Pose3D*>(container->getDomain()->getValue())){
                output_state.update( "|" + old_ident + ".value.orientation|");
            }
            else {
                output_state.update( "|" + old_ident + ".value.property|");
            }
        }
        else {
            auto member = this->operands[0]->getLinked();
            //auto iident_ = ident_map.count(member) ? (ident_map[member] = ++ident_map[member]) : (ident_map[member] = ident_++);
            auto val = this->operands[1];

            output_state.update( std::string("def ") );
            //member->buildString(false);
            output_state.update(getNextIdentifier(member) + " : " + (member->getType()) + " := "); 
            val->buildString();
        }
    }
    else if(nodeType=="ASSIGN_R4X4_AT_R3"){
        auto member = this->operands[0]->getLinked();//->getContainer();

        //auto old_name = ident_map.count(member) ? member->getCoords()->getName() + std::to_string((ident_map[member])) : member->getCoords()->getName();
        
        //auto iident_ = ident_map.count(member) ? (ident_map[member] = ++ident_map[member]) : (ident_map[member] = ident_++);
        auto val = this->operands[1];


        if(auto pose = dynamic_cast<domain::Pose3D*>(member->getDomain()->getValue())){
            output_state.update( std::string("def ") + getNextIdentifier(member)
                + " : " + (member->getType()) + " := |{\n\t\tposition:=("); 
            val->buildString();
            output_state.update(").value,\n\t\t.."+getLastIdentifier(member)+".value\n}|");

        }
        else{
            output_state.update( std::string("def ") + getNextIdentifier(member)
                + " : " + (member->getType()) + " := |{\n\t\t.."+getLastIdentifier(member)+"\n}|");

        }

    }
    else if(nodeType=="ASSIGN_R4X4_AT_R3X3" || nodeType == "ASSIGN_R4X4_AT_R4"){
        auto member = this->operands[0]->getLinked();
        //auto old_name = ident_map.count(member) ? member->getCoords()->getName() + std::to_string((ident_map[member])) : member->getCoords()->getName();

        //auto iident_ = ident_map.count(member) ? (ident_map[member] = ++ident_map[member]) : (ident_map[member] = ident_++);
        auto val = this->operands[1];
        if(auto pose = dynamic_cast<domain::Pose3D*>(member->getDomain()->getValue())){
            output_state.update( std::string("def ") + getNextIdentifier(member) 
                + " : " + (member->getType()) + " := |{\n\t\torientation:=("); 
            val->buildString();
            output_state.update(").value,\n\t\t.."+getLastIdentifier(member)+".value\n}|");
        }
        else{
            output_state.update( std::string("def ") + getNextIdentifier(member)
                + " : " + (member->getType()) + " := |{\n\t\t.."+getLastIdentifier(member)+"\n}|");

        }
    }
    /*

  (|(|((|mk_time WorldTime.value 100|).value -ᵥ 
    target_pose_in_baselink0.value.latest.timestamp : duration WorldTime.value)|)
    .value.coord| : scalar_expr) < timespan
    */
    else if(nodeType == "LT_R1_R1"){
        operands[0]->buildString();
        output_state.update("<");
        operands[1]->buildString();
    }
    else if(nodeType == "COORDS_R1"){
        auto inner_ = this->operands[0];
        if(auto dc = dynamic_cast<domain::Scalar*>(this->getValue())){
            output_state.update("(|(");
            inner_->buildString();
            output_state.update(".value.coord)|:scalar_expr)");
        }
        else
            inner_->buildString();
    }
    auto end = output_state.getCurrentLoc();

    this->setStartLocation(begin);
    this->setEndLocation(end);
}

bool Interp::hasValue(){
    return (this->hasLinked()?this->getLinked()->getDomain()->hasValue() : this->domain->hasValue());//(dc and dc->hasValue());
};

domain::DomainObject* Interp::getValue(){
    return (this->hasLinked()?this->getLinked()->getDomain()->getValue():this->domain->getValue());
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
        else if(auto asort = dynamic_cast<domain::Orientation3D*>(this->domain->getValue())){
            return std::string("orientation3d_expr ") + asort->getSpace()->getName();
        }
        else if(auto asrot = dynamic_cast<domain::Rotation3D*>(this->domain->getValue())){
            return std::string("rotation3d_expr ") + asrot->getSpace()->getName();
        }
        else if(auto aspose = dynamic_cast<domain::Pose3D*>(this->domain->getValue())){
            return std::string("pose3d_expr ") + aspose->getSpace()->getName();
        }
        else if(auto astrans = dynamic_cast<domain::Geom3DTransform*>(this->domain->getValue())){
            auto dom_ = astrans->getDomain();
            auto cod_ = astrans->getCodomain();
            return std::string("geom3d_transform_expr ") + dom_->getName() + " " + cod_->getName(); 
        }
        else if(auto asscalar = dynamic_cast<domain::Scalar*>(this->domain->getValue())){
            return std::string("scalar_expr");
        }
        else if(auto astspose = dynamic_cast<domain::TimeStampedPose3D*>(this->domain->getValue())){
            return std::string("timestamped_pose3d_expr ") 
                + astspose->getTime()->getSpace()->getName() + " "
                + astspose->getValue()->getSpace()->getName();
        }
        else if(auto aststr = dynamic_cast<domain::TimeStampedGeom3DTransform*>(this->domain->getValue())){
            return std::string("timestamped_geom3d_transform_expr ") 
                + aststr->getTime()->getSpace()->getName() + " "
                + aststr->getValue()->getDomain()->getName() + " "
                + aststr->getValue()->getCodomain()->getName();
        }
        else return "_";
    }
    else return "_";
};

/*
work in progress


*/
std::string Interp::toStringAST(std::vector<domain::CoordinateSpace*> spaces,std::vector<domain::TimeSeries*> series){
    std::string retval = "";
    ident_ = 0;
    ident_map.clear();
    output_state.reset();

    
    auto begin = output_state.update("import .lang.lang\n").first;
    output_state.update("open lang.time\nopen lang.geom1d\nopen lang.geom3d\nopen lang.series.geom3d\nopen lang.bool_expr\n");
    output_state.update("namespace peirce_output\nnoncomputable theory\n\n");

    for(auto space:spaces){
        if(auto dc = dynamic_cast<domain::StandardTimeCoordinateSpace*>(space)){
            output_state.update("def " + space->getName() + "_fr : time_frame_expr := |time_std_frame|\n");
            output_state.update("def " + space->getName() + " : time_space_expr " + space->getName() + "_fr := |time_std_space|\n\n");
        }
        if(auto dc = dynamic_cast<domain::DerivedTimeCoordinateSpace*>(space)){
            auto parentName = dc->getParent()->getName();
            auto originData = dc->getOrigin();
            auto basisData = dc->getBasis();
            output_state.update("def " + space->getName() + "_fr : time_frame_expr := \n");
            output_state.update(" let origin := |mk_time " + parentName + ".value " + std::to_string(originData[0]) + "| in\n");
            output_state.update(" let basis := |mk_duration " + parentName + ".value " + std::to_string(basisData[0][0]) + "| in\n");
            output_state.update(" mk_time_frame_expr origin basis\n");
            output_state.update("def " + space->getName() + " : time_space_expr " + space->getName() + "_fr := mk_time_space_expr " + space->getName() + "_fr\n\n");
        }
        if(auto dc = dynamic_cast<domain::StandardGeom1DCoordinateSpace*>(space)){
            output_state.update("def " + space->getName() + "_fr : geom1d_frame_expr := |geom1d_std_frame|\n");
            output_state.update("def " + space->getName() + " : geom1d_space_expr " + space->getName() + "_fr := |geom1d_std_space|\n\n");
        }
        if(auto dc = dynamic_cast<domain::DerivedGeom1DCoordinateSpace*>(space)){
            auto parentName = dc->getParent()->getName();
            auto originData = dc->getOrigin();
            auto basisData = dc->getBasis();
            output_state.update("def " + space->getName() + "_fr : geom1d_frame_expr := \n");
            output_state.update(" let origin := |mk_position1d " + parentName + ".value " + std::to_string(originData[0]) + "| in\n");
            output_state.update(" let basis := |mk_displacement1d " + parentName + ".value " + std::to_string(basisData[0][0]) + "| in\n");
            output_state.update(" mk_geom1d_frame_expr origin basis\n");
            output_state.update("def " + space->getName() + " : geom1d_space_expr " + space->getName() + "_fr := mk_geom1d_space_expr " + space->getName() + "_fr\n\n");
        }
        if(auto dc = dynamic_cast<domain::StandardGeom3DCoordinateSpace*>(space)){
            output_state.update("def " + space->getName() + "_fr : geom3d_frame_expr := |geom3d_std_frame|\n");
            output_state.update("def " + space->getName() + " : geom3d_space_expr " + space->getName() + "_fr := |geom3d_std_space|\n\n");
        }
        if(auto dc = dynamic_cast<domain::DerivedGeom3DCoordinateSpace*>(space)){
            auto parentName = dc->getParent()->getName();
            auto originData = dc->getOrigin();
            auto basisData = dc->getBasis();
            output_state.update("def " + space->getName() + "_fr : geom3d_frame_expr := \n");
            output_state.update(" let origin := |mk_position3d " + parentName + ".value " + std::to_string(originData[0])+ " " + std::to_string(originData[1])+ " " + std::to_string(originData[2]) + "| in\n");
            output_state.update(" let basis0 := |mk_displacement3d " + parentName + ".value " + std::to_string(basisData[0][0]) + " " + std::to_string(basisData[0][1]) + " " + std::to_string(basisData[0][2]) + "| in\n");
            output_state.update(" let basis1 := |mk_displacement3d " + parentName + ".value " + std::to_string(basisData[1][0]) + " " + std::to_string(basisData[1][1]) + " " + std::to_string(basisData[1][2]) + "| in\n");
            output_state.update(" let basis2 := |mk_displacement3d " + parentName + ".value " + std::to_string(basisData[2][0]) + " " + std::to_string(basisData[2][1]) + " " + std::to_string(basisData[2][2]) + "| in\n");
            output_state.update(" mk_geom3d_frame_expr origin basis0 basis1 basis2\n");
            output_state.update("def " + space->getName() + " : geom3d_space_expr " + space->getName() + "_fr := mk_geom3d_space_expr " + space->getName() + "_fr\n\n");
        }
    }
    for(auto ser: series)
    {
        if(auto dc = dynamic_cast<domain::Pose3DSeries*>(ser))
        {
            output_state.update("def " + dc->getName() + " : pose3d_series_expr "); 
            output_state.update(dc->getTimeSpace()->getName() + " " + dc->getSpace()->getName());
            output_state.update(" := ");

            auto values = dc->getValues();

            if(values.size() == 0){
                output_state.update("|mk_pose3d_discrete_empty _ _|\n");
            }
            else {
                output_state.update("|[\n\t\t");
                for(int i = 0;i<values.size();i++){
                    auto val_ = values[i];
                    auto astime = val_->getTime();
                    //⟨⟩

                    output_state.update("⟨(");
                    output_state.update( std::string("mk_time ") + astime->getSpace()->getName() + ".value " + std::to_string(astime->getValue()[0]) + "");
                    auto aspose = val_->getValue();
                    auto ort = aspose->getOrientation();
                    auto pos = aspose->getPosition();
                    output_state.update("),(");
                    output_state.update( std::string("mk_pose3d ") + aspose->getSpace()->getName() + ".value ");
                    output_state.update( std::string("\n\t\t(mk_orientation3d ") + ort->getSpace()->getName() + ".value "
                        + std::to_string(ort->getValue()[0]) + " " + std::to_string(ort->getValue()[1]) + " " + std::to_string(ort->getValue()[2]) + " " 
                        + std::to_string(ort->getValue()[3]) + " " + std::to_string(ort->getValue()[4]) + " " + std::to_string(ort->getValue()[5]) + " "
                        + std::to_string(ort->getValue()[6]) + " " + std::to_string(ort->getValue()[7]) + " " + std::to_string(ort->getValue()[8]) + ")");
                    output_state.update( std::string("\n\t\t(mk_position3d ") + pos->getSpace()->getName() + ".value " + std::to_string(pos->getValue()[0]) + " " + std::to_string(pos->getValue()[1]) + " " + std::to_string(pos->getValue()[2]) + ")");
                    output_state.update(")⟩");
                    if(i<values.size()-1)
                        output_state.update(",\n\t\t");
                }
                output_state.update("]|\n");
            }

            /*
            output_state.update(std::string("def ") + getNextIdentifier(var_) + ":=" + getLastIdentifier(var_));
            output_state.update(std::string("["));
            if(expr_->hasValue()){
                if(auto dci = dynamic_cast<domain::TimeStamped*>(expr_->getDomain()->getValue())){
                    output_state.update("((|");
                    auto astime = dci->getTime();
                    output_state.update( std::string("mk_time ") + astime->getSpace()->getName() + ".value " + std::to_string(astime->getValue()[0]));
                    auto exprbegin = output_state.getCurrentLoc();
                    output_state.update("|↦|");
                    if(auto astspose = dynamic_cast<domain::TimeStampedPose3D*>(dci)){
                        auto aspose = astspose->getValue();
                        auto ort = aspose->getOrientation();
                        auto pos = aspose->getPosition();
                        output_state.update( std::string("mk_pose3d ") + aspose->getSpace()->getName() + ".value ");
                        output_state.update( std::string("\n\t\t(mk_orientation3d ") + ort->getSpace()->getName() + ".value "
                            + std::to_string(ort->getValue()[0]) + " " + std::to_string(ort->getValue()[1]) + " " + std::to_string(ort->getValue()[2]) + " " 
                            + std::to_string(ort->getValue()[3]) + " " + std::to_string(ort->getValue()[4]) + " " + std::to_string(ort->getValue()[5]) + " "
                            + std::to_string(ort->getValue()[6]) + " " + std::to_string(ort->getValue()[7]) + " " + std::to_string(ort->getValue()[8]) + ")");
                        output_state.update( std::string("\n\t\t(mk_position3d ") + pos->getSpace()->getName() + ".value " + std::to_string(pos->getValue()[0]) + " " + std::to_string(pos->getValue()[1]) + " " + std::to_string(pos->getValue()[2]) + ")");
                    }
                    else if(auto aststrans = dynamic_cast<domain::TimeStampedGeom3DTransform*>(dci)){
                        auto astrans = aststrans->getValue();
                        auto dom_ = astrans->getDomain();
                        auto cod_ = astrans->getCodomain();
                        output_state.update( dom_->getName() + ".value.mk_geom3d_transform_to " + cod_->getName() + ".value");
                    }
                    else{
                        output_state.update("_");
                    }
            */
        }
        else if(auto dc = dynamic_cast<domain::Geom3DTransformSeries*>(ser))
        {
            output_state.update("def " + dc->getName() + " : geom3d_transform_series_expr "); 
            output_state.update(dc->getTimeSpace()->getName() + " " + dc->getDomain()->getName() + " " + dc->getCodomain()->getName());

            output_state.update(" := ");

            auto values = dc->getValues();

            if(values.size() == 0){
                output_state.update("|mk_geom3d_transform_discrete_empty _ _ _|\n");
            }
            else {
                output_state.update("|[\n\t\t");
                for(int i = 0;i<values.size();i++){
                    auto val_ = values[i];
                    auto astime = val_->getTime();
                    //⟨⟩

                    output_state.update("⟨(");
                    output_state.update( std::string("mk_time ") + astime->getSpace()->getName() + ".value " + std::to_string(astime->getValue()[0]) + "");
               
                    output_state.update("),(");
                    
                    auto astrans = val_->getValue();
                    auto dom_ = astrans->getDomain();
                    auto cod_ = astrans->getCodomain();
                    output_state.update( dom_->getName() + ".value.mk_geom3d_transform_to " + cod_->getName() + ".value");
                
                    output_state.update(")⟩");
                    if(i<values.size()-1)
                        output_state.update(",\n\t\t");
                }
                output_state.update("]|\n");
            }

        }
    }
    output_state.update("\n");
    for(auto op: this->body){
        auto nodeBegin = output_state.getCurrentLoc();
        op->buildString();
        //output_state.update(op->buildString() + "\n");
        auto nodeEnd = output_state.getCurrentLoc();
        op->setStartLocation(nodeBegin);
        op->setEndLocation(nodeEnd);
        output_state.update("\n");
    }
    output_state.update("\n\n");
    auto end = output_state.update("end peirce_output").second;

    this->setStartLocation(begin);
    this->setEndLocation(end);

    return output_state.getOutput();
}

} //namespace interp