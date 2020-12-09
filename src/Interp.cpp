#include "Interp.h"

#include "Domain.h"
#include "InterpToDomain.h"

#include <g3log/g3log.hpp>

#include <algorithm>
#include <unordered_map>

using namespace g3; 

namespace interp{

int GLOBAL_INDEX = 0;
std::unordered_map<Interp*,int> GLOBAL_IDS;
int ENV_INDEX = 0;
//this will get removed in the future once physlang stabilizes
interp2domain::InterpToDomain* i2d_;


std::string getEnvName(){
    return "env" + std::to_string(++ENV_INDEX);
};

std::string getLastEnv(){
    return "env" + std::to_string(ENV_INDEX - 1);
};

Interp::Interp(coords::Coords* c, domain::DomainObject* d) : coords_(c), dom_(d){
}

std::string Space::toString() const {
    std::string retval = "";
    bool found = false;
    
    int id = GLOBAL_IDS.count(const_cast<Space*>(this)) ? GLOBAL_IDS[const_cast<Space*>(this)] : GLOBAL_IDS[const_cast<Space*>(this)] = (GLOBAL_INDEX += 2); 
    

	if(auto dc = dynamic_cast<domain::EuclideanGeometry*>(s_)){
            found = true;
           // retval += "def " + dc->getName() + "var : lang.classicalGeometry.var := lang.classicalGeometry.var.mk " + std::to_string(id) + "" + "\n";
            //retval += "\ndef " + dc->getName() + "sp := lang.classicalGeometry.expr.lit (classicalGeometry.mk " + std::to_string(id-1) + " " + std::to_string(dc->getDimension()) + ")"; 
            retval += "\ndef " + dc->getName() + " := cmd.classicalGeometryAssmt (⟨⟨" + std::to_string(id) + "⟩⟩) (lang.classicalGeometry.spaceExpr.lit(classicalGeometry.build " + std::to_string(id) + " " + std::to_string(dc->getDimension()) + ")"")\n";
            retval += "\n def " + getEnvName() + " := cmdEval " + dc->getName() + " " + getLastEnv();
    }
	if(auto dc = dynamic_cast<domain::ClassicalTime*>(s_)){
            found = true;
           // retval += "def " + dc->getName() + "var : lang.classicalTime.var := lang.classicalTime.var.mk " + std::to_string(id) + "" + "\n";
            //retval += "\ndef " + dc->getName() + "sp := lang.classicalTime.expr.lit (classicalTime.mk " + std::to_string(id) + ")"; 
            retval += "\ndef " + dc->getName() + " := cmd.classicalTimeAssmt (⟨⟨" + std::to_string(id) + "⟩⟩) (lang.classicalTime.spaceExpr.lit(classicalTime.build " + std::to_string(id-1) + ")"")\n";
            retval += "\n def " + getEnvName() + " := cmdEval " + dc->getName() + " " + getLastEnv();
    }

    if(!found){
        //retval = "--Unknown space type - Translation Failed!";
    }

    return retval;
};

std::string Space::getVarExpr() const {
    
	if(auto dc = dynamic_cast<domain::EuclideanGeometry*>(s_)){
            int id = GLOBAL_IDS.count(const_cast<Space*>(this)) ? GLOBAL_IDS[const_cast<Space*>(this)] : GLOBAL_IDS[const_cast<Space*>(this)] = (GLOBAL_INDEX += 2); 
    
            return "lang.classicalGeometry.expr.var (lang.classicalGeometry.spaceVar.mk " + std::to_string(id) + ")";

    }
	if(auto dc = dynamic_cast<domain::ClassicalTime*>(s_)){
            int id = GLOBAL_IDS.count(const_cast<Space*>(this)) ? GLOBAL_IDS[const_cast<Space*>(this)] : GLOBAL_IDS[const_cast<Space*>(this)] = (GLOBAL_INDEX += 2); 
    
            return "lang.classicalTime.expr.var (lang.classicalTime.spaceVar.mk " + std::to_string(id) + ")";

    }
	if(auto dc = dynamic_cast<domain::ClassicalVelocity*>(s_)){
            int id = GLOBAL_IDS.count(const_cast<Space*>(this)) ? GLOBAL_IDS[const_cast<Space*>(this)] : GLOBAL_IDS[const_cast<Space*>(this)] = (GLOBAL_INDEX += 2); 
    
            return "lang.classicalVelocity.expr.var (lang.classicalVelocity.spaceVar.mk " + std::to_string(id) + ")";

    }
    return "";
}

std::string Space::getEvalExpr() const {
    auto lastEnv = getLastEnv();


	if(auto dc = dynamic_cast<domain::EuclideanGeometry*>(s_)){
            int id = GLOBAL_IDS.count(const_cast<Space*>(this)) ? GLOBAL_IDS[const_cast<Space*>(this)] : GLOBAL_IDS[const_cast<Space*>(this)] = (GLOBAL_INDEX += 2); 
    
            return "(classicalGeometryEval (lang.classicalGeometry.spaceExpr.var (lang.classicalGeometry.spaceVar.mk " + std::to_string(id) + ")) ( " + lastEnv + " ))";

    }
	if(auto dc = dynamic_cast<domain::ClassicalTime*>(s_)){
            int id = GLOBAL_IDS.count(const_cast<Space*>(this)) ? GLOBAL_IDS[const_cast<Space*>(this)] : GLOBAL_IDS[const_cast<Space*>(this)] = (GLOBAL_INDEX += 2); 
    
            return "(classicalTimeEval (lang.classicalTime.spaceExpr.var (lang.classicalTime.spaceVar.mk " + std::to_string(id) + ")) ( " + lastEnv + " ))";

    }
	if(auto dc = dynamic_cast<domain::ClassicalVelocity*>(s_)){
            int id = GLOBAL_IDS.count(const_cast<Space*>(this)) ? GLOBAL_IDS[const_cast<Space*>(this)] : GLOBAL_IDS[const_cast<Space*>(this)] = (GLOBAL_INDEX += 2); 
    
            return "(classicalVelocityEval (lang.classicalVelocity.spaceExpr.var (lang.classicalVelocity.spaceVar.mk " + std::to_string(id) + ")) ( " + lastEnv + " ))";

    }
    return "";
}

std::string DerivedSpace::toString() const {
    std::string retval = "";
    bool found = false;
    
    int id = GLOBAL_IDS.count(const_cast<DerivedSpace*>(this)) ? GLOBAL_IDS[const_cast<DerivedSpace*>(this)] : GLOBAL_IDS[const_cast<DerivedSpace*>(this)] = (GLOBAL_INDEX += 2); 
    

	if(auto dc = dynamic_cast<domain::ClassicalVelocity*>(s_)){
            found = true;
            auto currentEnv = getEnvName();
            //retval += "def " + dc->getName() + "var : lang.classicalVelocity.var := lang.classicalVelocity.var.mk " + std::to_string(id) + "" + "\n";
            //retval += "\ndef " + dc->getName() + "sp := lang.classicalVelocity.expr.lit (classicalVelocity.mk " + std::to_string(id) + " " + dc->getBase1()->getName() + " " + dc->getBase2()->getName() +  ")"; 
            retval += "\ndef " + dc->getName() + " := cmd.classicalVelocityFrameAssmt \n\t\t(lang.classicalVelocity.var.mk " + std::to_string(id) + ") \n\t\t(lang.classicalVelocity.expr.lit (classicalVelocity.mk " + std::to_string(id-1) + " \n\t\t\t" + this->base_1->getEvalExpr() + " \n\t\t\t" + this->base_2->getEvalExpr() +  "))\n";
            retval += "\n def " + currentEnv + " := cmdEval " + dc->getName() + " " + getLastEnv();
    }

    if(!found){
        //retval = "--Unknown space type - Translation Failed!";
    }

    return retval;


};

std::string MeasurementSystem::toString() const {
    std::string retval = "";
    
    int id = GLOBAL_IDS.count(const_cast<MeasurementSystem*>(this)) ? GLOBAL_IDS[const_cast<MeasurementSystem*>(this)] : GLOBAL_IDS[const_cast<MeasurementSystem*>(this)] = (GLOBAL_INDEX += 2); 
    
    if(((domain::SIMeasurementSystem*)this->ms_)){
        retval += "def " + this->ms_->getName() + " := cmd.measurementSystemAssmt (⟨⟨" + std::to_string(id) + "⟩⟩) (lang.measurementSystem.measureExpr.lit measurementSystem.si_measurement_system)";
        retval += "\n def " + getEnvName() + " := cmdEval " + this->ms_->getName() + " " + getLastEnv();
    }
    else if((domain::ImperialMeasurementSystem*)this->ms_){
        retval += "def " + this->ms_->getName() + " :=  cmd.measurementSystemAssmt (⟨⟨" + std::to_string(id) + "⟩⟩) (lang.measurementSystem.measureExpr.lit measurementSystem.imperial_measurement_system)";
        retval += "\n def " + getEnvName() + " := cmdEval " + this->ms_->getName() + " " + getLastEnv();

    }
        return retval;


};

std::string Frame::toString() const {
    std::string retval = "";
    
    int id = GLOBAL_IDS.count(const_cast<Frame*>(this)) ? GLOBAL_IDS[const_cast<Frame*>(this)] : GLOBAL_IDS[const_cast<Frame*>(this)] = (GLOBAL_INDEX += 2); 
    
    int sid = GLOBAL_IDS.count(const_cast<Space*>(sp_)) ? GLOBAL_IDS[const_cast<Space*>(sp_)] : GLOBAL_IDS[const_cast<Space*>(sp_)] = (GLOBAL_INDEX += 2); 
    
    int mid = GLOBAL_IDS.count(const_cast<MeasurementSystem*>(ms_)) ? GLOBAL_IDS[const_cast<MeasurementSystem*>(ms_)] : GLOBAL_IDS[const_cast<MeasurementSystem*>(ms_)] = (GLOBAL_INDEX += 2); 
    
    bool found = false;
    //bool isStandard = this->f_->getName() == "Standard";
    //if(!isStandard)
    //    return retval;

	if(auto dc = dynamic_cast<domain::EuclideanGeometryFrame*>(f_)){
        found = true;
        auto df = dynamic_cast<domain::EuclideanGeometryAliasedFrame*>(f_);
        retval += "\ndef " + ((domain::AliasedFrame*)df)->getName() + " := cmd.classicalGeometryFrameAssmt (⟨⟨" + std::to_string(id) + "⟩⟩) (lang.classicalGeometry.frameExpr.lit(classicalGeometryEval " + std::to_string(sid)  + ")"")\n";
        retval += "\n def " + getEnvName() + " := cmdEval " + ((domain::AliasedFrame*)df)->getName() + " " + getLastEnv();
    }
	if(auto dc = dynamic_cast<domain::ClassicalTimeFrame*>(f_)){
        found = true;
        auto df = dynamic_cast<domain::ClassicalTimeAliasedFrame*>(f_);
        retval += "\ndef " + ((domain::AliasedFrame*)df)->getName() + " := cmd.classicalTimeFrameAssmt (⟨⟨" + std::to_string(id) + "⟩⟩) (lang.classicalTime.frameExpr.lit(classicalTimeFrame.interpret (classicalTime.stdFrame (classicalTime.build " + std::to_string(sid-1) + ")) (measurementSystemEval (lang.measurementSystem.measureExpr.var ⟨⟨" + std::to_string(mid) + "⟩⟩) " + getLastEnv() + "))"")\n";
        retval += "\n def " + getEnvName() + " := cmdEval " + ((domain::AliasedFrame*)df)->getName() + " " + getLastEnv();
    }
	if(auto dc = dynamic_cast<domain::ClassicalVelocityFrame*>(f_)){
        found = true;
        auto df = dynamic_cast<domain::ClassicalVelocityAliasedFrame*>(f_);
        retval += "\ndef " + ((domain::AliasedFrame*)df)->getName() + " := cmd.classicalVelocityFrameAssmt (⟨⟨" + std::to_string(id) + "⟩⟩) (lang.classicalVelocity.frameExpr.lit(classicalVelocityEval " + std::to_string(sid)  + ")"")\n";
        retval += "\n def " + getEnvName() + " := cmdEval " + ((domain::AliasedFrame*)df)->getName() + " " + getLastEnv();
    }

    if(!found){
        //retval = "--Unknown Frame type - Translation Failed!";
    }

    return retval;

};


PROGRAM::PROGRAM(coords::PROGRAM* c, domain::DomainObject* d) : Interp(c,d) {}
                    
std::string PROGRAM::toString() const {
    std::string retval = "";
    bool found = false;
    
    retval = "Calling toString on a production, rather than a case.";
    
    
    return retval;
}
                
SEQ_GLOBALSTMT::SEQ_GLOBALSTMT(coords::SEQ_GLOBALSTMT* c, domain::DomainObject* d, std::vector<interp::GLOBALSTMT*> operands)  :PROGRAM(c, d) {
    for(auto& op : operands){
        this->operands_.push_back(op);
    }

};
std::string SEQ_GLOBALSTMT::toString() const{ 
    std::string retval = "";
    string cmdval = "[]";
    for(auto op: this->operands_){ 
        retval += "\n" + op->toString() + "\n";
        cmdval = op->coords_->toString() + "::" + cmdval;
    }
    cmdval = "(" + cmdval + ")";

    cmdval += ""; 
    cmdval = "\ndef " + this->coords_->toString() + " : PhysCommand := PhysCommand.Seq " + cmdval;


    retval += "\n" + cmdval + "\n";
    

    //std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {   
        retval.replace(index, singleperiod.length(), singleperiod); 
    }
    
    
    return retval;
}
std::string SEQ_GLOBALSTMT::toStringLinked(
        std::vector<interp::Space*> links, 
        std::vector<std::string> names, 
        std::vector<interp::MeasurementSystem*> msystems,
        std::vector<std::string> msnames,
        std::vector<interp::Frame*> framelinks, 
        std::vector<string> framenames, 
        interp2domain::InterpToDomain* i2d,
        bool before) { 
    //std::string toStr = this->toString();
    i2d_ = i2d;
    std::string retval = "";
    string cmdvalstart = "::[]";
    string cmdval = "";
    int i = 0;

    std::string cmdwrapper = "PhysCommand.Seq";

    //int count = this->operands_.size() + links.size() + framelinks.size();
    int actualcount = 0;
    if(true)
    {
        bool prev;

        for(auto op: links){
            if(prev){
                retval += "\n" + op->toString() + "\n";
                cmdval = "(" + cmdwrapper + " " + names[i++] + " " + cmdval + ")";
            }
            else{
                retval += "\n" + op->toString() + "\n";
                cmdval = names[i++];
                prev = true;
                
            }
            actualcount++;
        }
        i = 0;
        for(auto& ms : msystems){
            retval += "\n" + ms->toString() + "\n";
            cmdval = "(" + cmdwrapper + " " + msnames[i++] + " " + cmdval + ")";
            actualcount++;
        }

        i = 0;
        for(auto op: framelinks){
            if(prev){ 
                if((domain::AliasedFrame*)op->f_){
                retval += "\n" + op->toString() + "\n";
                auto df = dynamic_cast<domain::AliasedFrame*>(op->f_);
                cmdval = "(" + cmdwrapper + " " + df->getName() + " " + cmdval + ")";
                i++;
                }
                else if((domain::DerivedFrame*)op->f_){
                retval += "\n" + op->toString() + "\n";
                auto df = dynamic_cast<domain::DerivedFrame*>(op->f_);
                cmdval = "(" + cmdwrapper + " " + df->getName() + " " + cmdval + ")";
                i++;
                }
            }
            else {
                if((domain::AliasedFrame*)op->f_){
                retval += "\n" + op->toString() + "\n";
                cmdval = framenames[i++];
                prev = true;
                }
                else if((domain::DerivedFrame*)op->f_){
                retval += "\n" + op->toString() + "\n";
                cmdval = framenames[i++];
                prev = true;
                }
            }
        }

        //bool start = true;
        for(auto op: this->operands_){ 
            if(prev and op->coords_->codegen()){
                retval += "\n" + op->toString() + "\n";
                cmdval = "(" + cmdwrapper + " " + op->coords_->toString() + " " + cmdval + ")";
                actualcount++;
            }
            else if (op->coords_->codegen()){
                retval += "\n" + op->toString() + "\n";
                cmdval = op->coords_->toString();
                prev = true;
                actualcount++;
            }
            //retval += "\n" + op->toString() + "\n";
            //cmdval = cmdval + (!start?"::":"") + op->coords_->toString();
            //start = false;
        }
        
    }


    /*if(before)
    {
        
        for(auto op: links){
            retval += "\n" + op->toString() + "\n";
            cmdval = names[i++] + "::" + cmdval;
            
        }
        i = 0;
        for(auto op: framelinks){
            retval += "\n" + op->toString() + "\n";
            cmdval = framenames[i++] + "::" + cmdval;
        }

        bool start = true;
        for(auto op: this->operands_){ 
            retval += "\n" + op->toString() + "\n";
            cmdval = cmdval + (!start?"::":"") + op->coords_->toString();
            start = false;
        }
    }
    else
    {
        for(auto op: this->operands_){ 
            retval += "\n" + op->toString() + "\n";
            cmdval = op->coords_->toString() + "::" + cmdval;
        }
        bool start = true;
        for(auto op: links){
            retval += "\n" + op->toString() + "\n";
            cmdval = cmdval + (!start?"::":"") + names[i++];
            start = false;
            
        }
        i = 0;
        for(auto op: framelinks){
            retval += "\n" + op->toString() + "\n";
            cmdval = framenames[i++] + "::" + cmdval;
        }

    }*/
    //cmdval += ""; 
    //cmdval = "\ndef " + this->coords_->toString() + " : PhysCommand := PhysCommand.Seq " + cmdval;


    if(actualcount>1)
        retval += "\ndef " + this->coords_->toString() + " : PhysCommand :=" + cmdval + "\n";
    

    //std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {   
        retval.replace(index, singleperiod.length(), singleperiod); 
    }
    if(before)
    {
        
    }
    else
    {

    }

    return retval;
}


GLOBALSTMT::GLOBALSTMT(coords::GLOBALSTMT* c, domain::DomainObject* d) : Interp(c,d) {}
                    
std::string GLOBALSTMT::toString() const {
    std::string retval = "";
    bool found = false;
    
    retval = "Calling toString on a production, rather than a case.";
    
    
    return retval;
}
                
STMT::STMT(coords::STMT* c, domain::DomainObject* d) : Interp(c,d) {}
                    
std::string STMT::toString() const {
    std::string retval = "";
    bool found = false;
    
    retval = "Calling toString on a production, rather than a case.";
    
    
    return retval;
}
                
COMPOUND_STMT::COMPOUND_STMT(coords::COMPOUND_STMT* c, domain::DomainObject* d, std::vector<interp::STMT*> operands)  :STMT(c, d) {
    for(auto& op : operands){
        this->operands_.push_back(op);
    }

};
std::string COMPOUND_STMT::toString() const{ 
    std::string retval = "";
    string cmdval = "[]";
    for(auto op: this->operands_){ 
        retval += "\n" + op->toString() + "\n";
        cmdval = op->coords_->toString() + "::" + cmdval;
    }
    cmdval = "(" + cmdval + ")";

    cmdval += ""; 
    cmdval = "\ndef " + this->coords_->toString() + " : cmd := cmd.seq " + cmdval;


    retval += "\n" + cmdval + "\n";
    

    //std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {   
        retval.replace(index, singleperiod.length(), singleperiod); 
    }
    
    
    return retval;
}
std::string COMPOUND_STMT::toStringLinked(
        std::vector<interp::Space*> links, 
        std::vector<std::string> names, 
        std::vector<interp::MeasurementSystem*> msystems,
        std::vector<std::string> msnames,
        std::vector<interp::Frame*> framelinks, 
        std::vector<string> framenames, 
        interp2domain::InterpToDomain* i2d,
        bool before) { 
    //std::string toStr = this->toString();
    i2d_ = i2d;
    std::string retval = "";
    string cmdvalstart = "::[]";
    string cmdval = "";
    int i = 0;

    std::string cmdwrapper = "cmd.seq";

    //int count = this->operands_.size() + links.size() + framelinks.size();
    int actualcount = 0;
    if(true)
    {
        bool prev;

        for(auto op: links){
            if(prev){
                retval += "\n" + op->toString() + "\n";
                cmdval = "(" + cmdwrapper + " " + names[i++] + " " + cmdval + ")";
            }
            else{
                retval += "\n" + op->toString() + "\n";
                cmdval = names[i++];
                prev = true;
                
            }
            actualcount++;
        }
        i = 0;
        for(auto& ms : msystems){
            retval += "\n" + ms->toString() + "\n";
            cmdval = "(" + cmdwrapper + " " + msnames[i++] + " " + cmdval + ")";
            actualcount++;
        }

        i = 0;
        for(auto op: framelinks){
            if(prev){ 
                if((domain::AliasedFrame*)op->f_){
                retval += "\n" + op->toString() + "\n";
                auto df = dynamic_cast<domain::AliasedFrame*>(op->f_);
                cmdval = "(" + cmdwrapper + " " + df->getName() + " " + cmdval + ")";
                i++;
                }
                else if((domain::DerivedFrame*)op->f_){
                retval += "\n" + op->toString() + "\n";
                auto df = dynamic_cast<domain::DerivedFrame*>(op->f_);
                cmdval = "(" + cmdwrapper + " " + df->getName() + " " + cmdval + ")";
                i++;
                }
            }
            else {
                if((domain::AliasedFrame*)op->f_){
                retval += "\n" + op->toString() + "\n";
                cmdval = framenames[i++];
                prev = true;
                }
                else if((domain::DerivedFrame*)op->f_){
                retval += "\n" + op->toString() + "\n";
                cmdval = framenames[i++];
                prev = true;
                }
            }
        }

        //bool start = true;
        for(auto op: this->operands_){ 
            if(prev and op->coords_->codegen()){
                retval += "\n" + op->toString() + "\n";
                cmdval = "(" + cmdwrapper + " " + op->coords_->toString() + " " + cmdval + ")";
                actualcount++;
            }
            else if (op->coords_->codegen()){
                retval += "\n" + op->toString() + "\n";
                cmdval = op->coords_->toString();
                prev = true;
                actualcount++;
            }
            //retval += "\n" + op->toString() + "\n";
            //cmdval = cmdval + (!start?"::":"") + op->coords_->toString();
            //start = false;
        }
        
    }


    /*if(before)
    {
        
        for(auto op: links){
            retval += "\n" + op->toString() + "\n";
            cmdval = names[i++] + "::" + cmdval;
            
        }
        i = 0;
        for(auto op: framelinks){
            retval += "\n" + op->toString() + "\n";
            cmdval = framenames[i++] + "::" + cmdval;
        }

        bool start = true;
        for(auto op: this->operands_){ 
            retval += "\n" + op->toString() + "\n";
            cmdval = cmdval + (!start?"::":"") + op->coords_->toString();
            start = false;
        }
    }
    else
    {
        for(auto op: this->operands_){ 
            retval += "\n" + op->toString() + "\n";
            cmdval = op->coords_->toString() + "::" + cmdval;
        }
        bool start = true;
        for(auto op: links){
            retval += "\n" + op->toString() + "\n";
            cmdval = cmdval + (!start?"::":"") + names[i++];
            start = false;
            
        }
        i = 0;
        for(auto op: framelinks){
            retval += "\n" + op->toString() + "\n";
            cmdval = framenames[i++] + "::" + cmdval;
        }

    }*/
    //cmdval += ""; 
    //cmdval = "\ndef " + this->coords_->toString() + " : cmd := cmd.seq " + cmdval;


    if(actualcount>1)
        retval += "\ndef " + this->coords_->toString() + " : cmd :=" + cmdval + "\n";
    

    //std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {   
        retval.replace(index, singleperiod.length(), singleperiod); 
    }
    if(before)
    {
        
    }
    else
    {

    }

    return retval;
}


FUNC_DECL::FUNC_DECL(coords::FUNC_DECL* c, domain::DomainObject* d) : GLOBALSTMT(c,d) {}
                    
std::string FUNC_DECL::toString() const {
    std::string retval = "";
    bool found = false;
    
    retval = "Calling toString on a production, rather than a case.";
    
    
    return retval;
}
                

VOID_FUNC_DECL_STMT::VOID_FUNC_DECL_STMT(coords::VOID_FUNC_DECL_STMT* c, domain::DomainObject* d,interp::STMT * operand1 ) : FUNC_DECL(c,d)
   ,operand_1(operand1) {}

std::string VOID_FUNC_DECL_STMT::toString() const {
                        std::string retval = "";
                        bool found = false;

                

    if (!found){
                        //ret = "";
                        
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {
        retval.replace(index, sub_str.length(), sub_str);
    }
    while ((index = retval.find(": ^")) != string::npos)
    {
        retval.replace(index, sub_str.length(), sub_str);
    }
    while ((index = retval.find("..")) != string::npos)
    {
        retval.replace(index, singleperiod.length(), singleperiod);
    }


                    return retval;
                }
                


MAIN_FUNC_DECL_STMT::MAIN_FUNC_DECL_STMT(coords::MAIN_FUNC_DECL_STMT* c, domain::DomainObject* d,interp::STMT * operand1 ) : FUNC_DECL(c,d)
   ,operand_1(operand1) {}

std::string MAIN_FUNC_DECL_STMT::toString() const {
                        std::string retval = "";
                        bool found = false;

                

    if (!found){
                        //ret = "";
                        
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {
        retval.replace(index, sub_str.length(), sub_str);
    }
    while ((index = retval.find(": ^")) != string::npos)
    {
        retval.replace(index, sub_str.length(), sub_str);
    }
    while ((index = retval.find("..")) != string::npos)
    {
        retval.replace(index, singleperiod.length(), singleperiod);
    }


                    return retval;
                }
                

DECLARE::DECLARE(coords::DECLARE* c, domain::DomainObject* d) : STMT(c,d) {}
                    
std::string DECLARE::toString() const {
    std::string retval = "";
    bool found = false;
    
    retval = "Calling toString on a production, rather than a case.";
    
    
    return retval;
}
                

DECL_REAL1_VAR_REAL1_EXPR::DECL_REAL1_VAR_REAL1_EXPR(coords::DECL_REAL1_VAR_REAL1_EXPR* c, domain::DomainObject* d,interp::REAL1_VAR_IDENT * operand1,interp::REAL1_EXPR * operand2 ) : DECLARE(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string DECL_REAL1_VAR_REAL1_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(this->operand_2->dom_)){
        
        auto env = getEnvName();
        retval += "def " + this->coords_->toString() + " := cmd.classicalVelocityCoordinateVectorAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
            
        retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(this->operand_2->dom_)){
        
        auto env = getEnvName();
        retval += "def " + this->coords_->toString() + " := cmd.classicalTimeCoordinateVectorAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
            
        retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(this->operand_2->dom_)){
        
        auto env = getEnvName();
        retval += "def " + this->coords_->toString() + " := cmd.classicalGeometryCoordinateVectorAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
            
        retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(this->operand_2->dom_)){
        
        auto env = getEnvName();
        retval += "def " + this->coords_->toString() + " := cmd.classicalTimeCoordinatePointAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
            
        retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(this->operand_2->dom_)){
        
        auto env = getEnvName();
        retval += "def " + this->coords_->toString() + " := cmd.classicalGeometryCoordinatePointAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
            
        retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
    }
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->operand_2->dom_)){
        if(cont->hasValue()){
                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(cont->getValue())){
                auto env = getEnvName();
                retval += "def " + this->coords_->toString() + " := cmd.classicalVelocityCoordinateVectorAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
                
                retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(cont->getValue())){
                auto env = getEnvName();
                retval += "def " + this->coords_->toString() + " := cmd.classicalTimeCoordinateVectorAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
                
                retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(cont->getValue())){
                auto env = getEnvName();
                retval += "def " + this->coords_->toString() + " := cmd.classicalGeometryCoordinateVectorAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
                
                retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(cont->getValue())){
                auto env = getEnvName();
                retval += "def " + this->coords_->toString() + " := cmd.classicalTimeCoordinatePointAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
                
                retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(cont->getValue())){
                auto env = getEnvName();
                retval += "def " + this->coords_->toString() + " := cmd.classicalGeometryCoordinatePointAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
                
                retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
            }
        }
    }
    //    }
    //}

    if(!found){
        //retval = "";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod);
    }
    

    return retval;
}
                


DECL_REAL3_VAR_REAL3_EXPR::DECL_REAL3_VAR_REAL3_EXPR(coords::DECL_REAL3_VAR_REAL3_EXPR* c, domain::DomainObject* d,interp::REAL3_VAR_IDENT * operand1,interp::REAL3_EXPR * operand2 ) : DECLARE(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string DECL_REAL3_VAR_REAL3_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(this->operand_2->dom_)){
        
        auto env = getEnvName();
        retval += "def " + this->coords_->toString() + " := cmd.classicalVelocityCoordinateVectorAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
            
        retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(this->operand_2->dom_)){
        
        auto env = getEnvName();
        retval += "def " + this->coords_->toString() + " := cmd.classicalTimeCoordinateVectorAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
            
        retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(this->operand_2->dom_)){
        
        auto env = getEnvName();
        retval += "def " + this->coords_->toString() + " := cmd.classicalGeometryCoordinateVectorAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
            
        retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(this->operand_2->dom_)){
        
        auto env = getEnvName();
        retval += "def " + this->coords_->toString() + " := cmd.classicalTimeCoordinatePointAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
            
        retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(this->operand_2->dom_)){
        
        auto env = getEnvName();
        retval += "def " + this->coords_->toString() + " := cmd.classicalGeometryCoordinatePointAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
            
        retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
    }
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->operand_2->dom_)){
        if(cont->hasValue()){
                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(cont->getValue())){
                auto env = getEnvName();
                retval += "def " + this->coords_->toString() + " := cmd.classicalVelocityCoordinateVectorAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
                
                retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(cont->getValue())){
                auto env = getEnvName();
                retval += "def " + this->coords_->toString() + " := cmd.classicalTimeCoordinateVectorAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
                
                retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(cont->getValue())){
                auto env = getEnvName();
                retval += "def " + this->coords_->toString() + " := cmd.classicalGeometryCoordinateVectorAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
                
                retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(cont->getValue())){
                auto env = getEnvName();
                retval += "def " + this->coords_->toString() + " := cmd.classicalTimeCoordinatePointAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
                
                retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(cont->getValue())){
                auto env = getEnvName();
                retval += "def " + this->coords_->toString() + " := cmd.classicalGeometryCoordinatePointAssmt (" + this->operand_1->toString() + ") (" + this->operand_2->toString() +")\n";
                
                retval += "def " + env + " := cmdEval " + this->coords_->toString() + " " + getLastEnv();
            }
        }
    }
    //    }
    //}

    if(!found){
        //retval = "";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod);
    }
    

    return retval;
}
                


DECL_REAL1_VAR::DECL_REAL1_VAR(coords::DECL_REAL1_VAR* c, domain::DomainObject* d,interp::REAL1_VAR_IDENT * operand1 ) : DECLARE(c,d)
   ,operand_1(operand1) {}

std::string DECL_REAL1_VAR::toString() const {
    bool found = false;
    std::string retval = "";
    //    }
    //}

    if(!found){
        //retval = "";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod);
    }
    

    return retval;
}
                


DECL_REAL3_VAR::DECL_REAL3_VAR(coords::DECL_REAL3_VAR* c, domain::DomainObject* d,interp::REAL3_VAR_IDENT * operand1 ) : DECLARE(c,d)
   ,operand_1(operand1) {}

std::string DECL_REAL3_VAR::toString() const {
    bool found = false;
    std::string retval = "";
    //    }
    //}

    if(!found){
        //retval = "";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod);
    }
    

    return retval;
}
                

REXPR::REXPR(coords::REXPR* c, domain::DomainObject* d) : STMT(c,d) {}
                    
std::string REXPR::toString() const {
    std::string retval = "";
    bool found = false;
    
    retval = "Calling toString on a production, rather than a case.";
    
    
    return retval;
}
                
LEXPR::LEXPR(coords::LEXPR* c, domain::DomainObject* d) : STMT(c,d) {}
                    
std::string LEXPR::toString() const {
    std::string retval = "";
    bool found = false;
    
    retval = "Calling toString on a production, rather than a case.";
    
    
    return retval;
}
                
REAL3_EXPR::REAL3_EXPR(coords::REAL3_EXPR* c, domain::DomainObject* d) : REXPR(c,d) {}
                    
std::string REAL3_EXPR::toString() const {
    std::string retval = "";
    bool found = false;
    
    retval = "Calling toString on a production, rather than a case.";
    
    
    return retval;
}
                

std::string REF_REAL3_VAR::toEvalString() const {
                        std::string retval = "";
                        bool found = false;
        
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        retval += "(classicalVelocityCoordinateVectorEval (lang.classicalVelocity.CoordinateVectorExpr.var ";
        retval += this->operand_1->toString();
        retval += ") " + env +")";
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        retval += "(classicalTimeCoordinateVectorEval (lang.classicalTime.CoordinateVectorExpr.var ";
        retval += this->operand_1->toString();
        retval += ") " + env +")";
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        retval += "(classicalGeometryCoordinateVectorEval (lang.classicalGeometry.CoordinateVectorExpr.var ";
        retval += this->operand_1->toString();
        retval += ") " + env +")";
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        retval += "(classicalTimeCoordinatePointEval (lang.classicalTime.CoordinatePointExpr.var ";
        retval += this->operand_1->toString();
        retval += ") " + env +")";
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        retval += "(classicalGeometryCoordinatePointEval (lang.classicalGeometry.CoordinatePointExpr.var ";
        retval += this->operand_1->toString();
        retval += ") " + env +")";
    }
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){
                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(cont->getValue())){
                
                auto env = getLastEnv();
                retval += "(classicalVelocityCoordinateVectorEval (lang.classicalVelocity.CoordinateVectorExpr.var ";
                retval += this->operand_1->toString();
                retval += ") " + env +")";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(cont->getValue())){
                
                auto env = getLastEnv();
                retval += "(classicalTimeCoordinateVectorEval (lang.classicalTime.CoordinateVectorExpr.var ";
                retval += this->operand_1->toString();
                retval += ") " + env +")";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(cont->getValue())){
                
                auto env = getLastEnv();
                retval += "(classicalGeometryCoordinateVectorEval (lang.classicalGeometry.CoordinateVectorExpr.var ";
                retval += this->operand_1->toString();
                retval += ") " + env +")";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(cont->getValue())){
                
                auto env = getLastEnv();
                retval += "(classicalTimeCoordinatePointEval (lang.classicalTime.CoordinatePointExpr.var ";
                retval += this->operand_1->toString();
                retval += ") " + env +")";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(cont->getValue())){
                
                auto env = getLastEnv();
                retval += "(classicalGeometryCoordinatePointEval (lang.classicalGeometry.CoordinatePointExpr.var ";
                retval += this->operand_1->toString();
                retval += ") " + env +")";
            }
        }
    }


    if (!found)
                                    {
                                        //ret = "";
                                        
    }
                                    std::replace(retval.begin(), retval.end(), '_', '.');
                                    std::size_t index;
                                    string sub_str = ": _";
                                    string singleperiod = ".a";
                                    while ((index = retval.find(": .")) != string::npos)
                                    {
                                        retval.replace(index, sub_str.length(), sub_str);
                                    }
                                    while ((index = retval.find(": ^")) != string::npos)
                                    {
                                        retval.replace(index, sub_str.length(), sub_str);
                                    }
                                    while ((index = retval.find("..")) != string::npos)
                                    {
                                        retval.replace(index, singleperiod.length(), singleperiod);
                                    }


                                    return retval;
                                }
                                

std::string REF_REAL3_VAR::toAlgebraString() const {
                        std::string retval = "";
                        bool found = false;

                        //  ret += "(";
                        //ret += "def var_" + std::to_string(++GLOBAL_INDEX) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL3_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalVelocityCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL3_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL3_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL3_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinatePointAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL3_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinatePointAlgebra " + this->toEvalString() + ")";
        
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL3_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalVelocityCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL3_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL3_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL3_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinatePointAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL3_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL3_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinatePointAlgebra " + this->toEvalString() + ")";
        
            }
        }
    }

    if(!found){
        //ret = "";
        
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod); 
    }
    
    
    return retval;
}
                

REF_REAL3_VAR::REF_REAL3_VAR(coords::REF_REAL3_VAR* c, domain::DomainObject* d,interp::REAL3_VAR_IDENT * operand1 ) : REAL3_EXPR(c,d)
   ,operand_1(operand1) {}

std::string REF_REAL3_VAR::toString() const {
    bool found = false;
    std::string retval = "";
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        retval += "(ClassicalVelocityCoordinateVectorExpr.var ";
        retval += this->operand_1->toString();
        retval += ")";
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        retval += "(ClassicalTimeCoordinateVectorExpr.var ";
        retval += this->operand_1->toString();
        retval += ")";
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        retval += "(EuclideanGeometryCoordinateVectorExpr.var ";
        retval += this->operand_1->toString();
        retval += ")";
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        retval += "(ClassicalTimeCoordinatePointExpr.var ";
        retval += this->operand_1->toString();
        retval += ")";
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        retval += "(EuclideanGeometryCoordinatePointExpr.var ";
        retval += this->operand_1->toString();
        retval += ")";
    }
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){
                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
                retval += "(ClassicalVelocityCoordinateVectorExpr.var ";
                retval += this->operand_1->toString();
                retval += ")";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
                retval += "(ClassicalTimeCoordinateVectorExpr.var ";
                retval += this->operand_1->toString();
                retval += ")";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
                retval += "(EuclideanGeometryCoordinateVectorExpr.var ";
                retval += this->operand_1->toString();
                retval += ")";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(cont->getValue())){
                found = true;
                retval += "(ClassicalTimeCoordinatePointExpr.var ";
                retval += this->operand_1->toString();
                retval += ")";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(cont->getValue())){
                found = true;
                retval += "(EuclideanGeometryCoordinatePointExpr.var ";
                retval += this->operand_1->toString();
                retval += ")";
            }
        }
    }


    //    }
    //}

    if(!found){
        //retval = "";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod);
    }
    

    return retval;
}
                


std::string ADD_REAL3_EXPR_REAL3_EXPR::toEvalString() const {
                        std::string retval = "";
                        bool found = false;
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalVelocityCoordinateVector.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinateVector.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinateVector.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinatePoint.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinatePoint.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
    }
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){
                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalVelocityCoordinateVector.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinateVector.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinateVector.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinatePoint.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinatePoint.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
            }
        }
    }


    if (!found)
                                    {
                                        //ret = "";
                                        
    }
                                    std::replace(retval.begin(), retval.end(), '_', '.');
                                    std::size_t index;
                                    string sub_str = ": _";
                                    string singleperiod = ".a";
                                    while ((index = retval.find(": .")) != string::npos)
                                    {
                                        retval.replace(index, sub_str.length(), sub_str);
                                    }
                                    while ((index = retval.find(": ^")) != string::npos)
                                    {
                                        retval.replace(index, sub_str.length(), sub_str);
                                    }
                                    while ((index = retval.find("..")) != string::npos)
                                    {
                                        retval.replace(index, singleperiod.length(), singleperiod);
                                    }


                                    return retval;
                                }
                                

std::string ADD_REAL3_EXPR_REAL3_EXPR::toAlgebraString() const {
                        std::string retval = "";
                        bool found = false;

                        //  ret += "(";
                        //ret += "def var_" + std::to_string(++GLOBAL_INDEX) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalVelocityCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinatePointAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinatePointAlgebra " + this->toEvalString() + ")";
        
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalVelocityCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinatePointAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinatePointAlgebra " + this->toEvalString() + ")";
        
            }
        }
    }

    if(!found){
        //ret = "";
        
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod); 
    }
    
    
    return retval;
}
                

ADD_REAL3_EXPR_REAL3_EXPR::ADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* c, domain::DomainObject* d,interp::REAL3_EXPR * operand1,interp::REAL3_EXPR * operand2 ) : REAL3_EXPR(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string ADD_REAL3_EXPR_REAL3_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += " (lang.classicalVelocity.CoordinateVectorExpr.lit \n";
        retval += "(classicalVelocityCoordinateVector.fromalgebra ";
        retval += std::string("(classicalVelocityEval ") + "(lang.classicalVelocity.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalVelocityFrameEval ") + "(lang.classicalVelocity.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += " (lang.classicalTime.CoordinateVectorExpr.lit \n";
        retval += "(classicalTimeCoordinateVector.fromalgebra ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += " (lang.classicalGeometry.CoordinateVectorExpr.lit \n";
        retval += "(classicalGeometryCoordinateVector.fromalgebra ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += " (lang.classicalTime.CoordinatePointExpr.lit \n";
        retval += "(classicalTimeCoordinatePoint.fromalgebra ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL3_EXPR_REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL3_EXPR_REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += " (lang.classicalGeometry.CoordinatePointExpr.lit \n";
        retval += "(classicalGeometryCoordinatePoint.fromalgebra ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
    }
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){
                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
                retval += " (lang.classicalVelocity.CoordinateVectorExpr.lit \n";
        retval += "(classicalVelocityCoordinateVector.fromalgebra ";
        retval += std::string("(classicalVelocityEval ") + "(lang.classicalVelocity.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalVelocityFrameEval ") + "(lang.classicalVelocity.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
                retval += " (lang.classicalTime.CoordinateVectorExpr.lit \n";
        retval += "(classicalTimeCoordinateVector.fromalgebra ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
                retval += " (lang.classicalGeometry.CoordinateVectorExpr.lit \n";
        retval += "(classicalGeometryCoordinateVector.fromalgebra ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
                retval += " (lang.classicalTime.CoordinatePointExpr.lit \n";
        retval += "(classicalTimeCoordinatePoint.fromalgebra ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
                retval += " (lang.classicalGeometry.CoordinatePointExpr.lit \n";
        retval += "(classicalGeometryCoordinatePoint.fromalgebra ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
            }
        }
    }


    //    }
    //}

    if(!found){
        //retval = "";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod);
    }
    

    return retval;
}
                

REAL3_LEXPR::REAL3_LEXPR(coords::REAL3_LEXPR* c, domain::DomainObject* d) : LEXPR(c,d) {}
                    
std::string REAL3_LEXPR::toString() const {
    std::string retval = "";
    bool found = false;
    
    retval = "Calling toString on a production, rather than a case.";
    
    
    return retval;
}
                

std::string LREF_REAL3_VAR::toEvalString() const {
                        std::string retval = "";
                        bool found = false;
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){
                        
        }
    }


    if (!found)
                                    {
                                        //ret = "";
                                        
    }
                                    std::replace(retval.begin(), retval.end(), '_', '.');
                                    std::size_t index;
                                    string sub_str = ": _";
                                    string singleperiod = ".a";
                                    while ((index = retval.find(": .")) != string::npos)
                                    {
                                        retval.replace(index, sub_str.length(), sub_str);
                                    }
                                    while ((index = retval.find(": ^")) != string::npos)
                                    {
                                        retval.replace(index, sub_str.length(), sub_str);
                                    }
                                    while ((index = retval.find("..")) != string::npos)
                                    {
                                        retval.replace(index, singleperiod.length(), singleperiod);
                                    }


                                    return retval;
                                }
                                

std::string LREF_REAL3_VAR::toAlgebraString() const {
                        std::string retval = "";
                        bool found = false;

                        //  ret += "(";
                        //ret += "def var_" + std::to_string(++GLOBAL_INDEX) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //ret = "";
        
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod); 
    }
    
    
    return retval;
}
                

LREF_REAL3_VAR::LREF_REAL3_VAR(coords::LREF_REAL3_VAR* c, domain::DomainObject* d,interp::REAL3_VAR_IDENT * operand1 ) : REAL3_LEXPR(c,d)
   ,operand_1(operand1) {}

std::string LREF_REAL3_VAR::toString() const {
    bool found = false;
    std::string retval = "";
    //    }
    //}

    if(!found){
        //retval = "";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod);
    }
    

    return retval;
}
                

REAL1_EXPR::REAL1_EXPR(coords::REAL1_EXPR* c, domain::DomainObject* d) : REXPR(c,d) {}
                    
std::string REAL1_EXPR::toString() const {
    std::string retval = "";
    bool found = false;
    
    retval = "Calling toString on a production, rather than a case.";
    
    
    return retval;
}
                

std::string REF_REAL1_VAR::toEvalString() const {
                        std::string retval = "";
                        bool found = false;
        
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        retval += "(classicalVelocityCoordinateVectorEval (lang.classicalVelocity.CoordinateVectorExpr.var ";
        retval += this->operand_1->toString();
        retval += ") " + env +")";
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        retval += "(classicalTimeCoordinateVectorEval (lang.classicalTime.CoordinateVectorExpr.var ";
        retval += this->operand_1->toString();
        retval += ") " + env +")";
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        retval += "(classicalGeometryCoordinateVectorEval (lang.classicalGeometry.CoordinateVectorExpr.var ";
        retval += this->operand_1->toString();
        retval += ") " + env +")";
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        retval += "(classicalTimeCoordinatePointEval (lang.classicalTime.CoordinatePointExpr.var ";
        retval += this->operand_1->toString();
        retval += ") " + env +")";
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        retval += "(classicalGeometryCoordinatePointEval (lang.classicalGeometry.CoordinatePointExpr.var ";
        retval += this->operand_1->toString();
        retval += ") " + env +")";
    }
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){
                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(cont->getValue())){
                
                auto env = getLastEnv();
                retval += "(classicalVelocityCoordinateVectorEval (lang.classicalVelocity.CoordinateVectorExpr.var ";
                retval += this->operand_1->toString();
                retval += ") " + env +")";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(cont->getValue())){
                
                auto env = getLastEnv();
                retval += "(classicalTimeCoordinateVectorEval (lang.classicalTime.CoordinateVectorExpr.var ";
                retval += this->operand_1->toString();
                retval += ") " + env +")";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(cont->getValue())){
                
                auto env = getLastEnv();
                retval += "(classicalGeometryCoordinateVectorEval (lang.classicalGeometry.CoordinateVectorExpr.var ";
                retval += this->operand_1->toString();
                retval += ") " + env +")";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(cont->getValue())){
                
                auto env = getLastEnv();
                retval += "(classicalTimeCoordinatePointEval (lang.classicalTime.CoordinatePointExpr.var ";
                retval += this->operand_1->toString();
                retval += ") " + env +")";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(cont->getValue())){
                
                auto env = getLastEnv();
                retval += "(classicalGeometryCoordinatePointEval (lang.classicalGeometry.CoordinatePointExpr.var ";
                retval += this->operand_1->toString();
                retval += ") " + env +")";
            }
        }
    }


    if (!found)
                                    {
                                        //ret = "";
                                        
    }
                                    std::replace(retval.begin(), retval.end(), '_', '.');
                                    std::size_t index;
                                    string sub_str = ": _";
                                    string singleperiod = ".a";
                                    while ((index = retval.find(": .")) != string::npos)
                                    {
                                        retval.replace(index, sub_str.length(), sub_str);
                                    }
                                    while ((index = retval.find(": ^")) != string::npos)
                                    {
                                        retval.replace(index, sub_str.length(), sub_str);
                                    }
                                    while ((index = retval.find("..")) != string::npos)
                                    {
                                        retval.replace(index, singleperiod.length(), singleperiod);
                                    }


                                    return retval;
                                }
                                

std::string REF_REAL1_VAR::toAlgebraString() const {
                        std::string retval = "";
                        bool found = false;

                        //  ret += "(";
                        //ret += "def var_" + std::to_string(++GLOBAL_INDEX) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL1_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalVelocityCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL1_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL1_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL1_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinatePointAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL1_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinatePointAlgebra " + this->toEvalString() + ")";
        
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL1_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalVelocityCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL1_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL1_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL1_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinatePointAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REF_REAL1_VAR*>(this)) ? GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] : GLOBAL_IDS[const_cast<REF_REAL1_VAR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinatePointAlgebra " + this->toEvalString() + ")";
        
            }
        }
    }

    if(!found){
        //ret = "";
        
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod); 
    }
    
    
    return retval;
}
                

REF_REAL1_VAR::REF_REAL1_VAR(coords::REF_REAL1_VAR* c, domain::DomainObject* d,interp::REAL1_VAR_IDENT * operand1 ) : REAL1_EXPR(c,d)
   ,operand_1(operand1) {}

std::string REF_REAL1_VAR::toString() const {
    bool found = false;
    std::string retval = "";
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        retval += "(ClassicalVelocityCoordinateVectorExpr.var ";
        retval += this->operand_1->toString();
        retval += ")";
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        retval += "(ClassicalTimeCoordinateVectorExpr.var ";
        retval += this->operand_1->toString();
        retval += ")";
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        retval += "(EuclideanGeometryCoordinateVectorExpr.var ";
        retval += this->operand_1->toString();
        retval += ")";
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        retval += "(ClassicalTimeCoordinatePointExpr.var ";
        retval += this->operand_1->toString();
        retval += ")";
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        retval += "(EuclideanGeometryCoordinatePointExpr.var ";
        retval += this->operand_1->toString();
        retval += ")";
    }
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){
                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(cont->getValue())){
                found = true;
                retval += "(ClassicalVelocityCoordinateVectorExpr.var ";
                retval += this->operand_1->toString();
                retval += ")";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(cont->getValue())){
                found = true;
                retval += "(ClassicalTimeCoordinateVectorExpr.var ";
                retval += this->operand_1->toString();
                retval += ")";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(cont->getValue())){
                found = true;
                retval += "(EuclideanGeometryCoordinateVectorExpr.var ";
                retval += this->operand_1->toString();
                retval += ")";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(cont->getValue())){
                found = true;
                retval += "(ClassicalTimeCoordinatePointExpr.var ";
                retval += this->operand_1->toString();
                retval += ")";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(cont->getValue())){
                found = true;
                retval += "(EuclideanGeometryCoordinatePointExpr.var ";
                retval += this->operand_1->toString();
                retval += ")";
            }
        }
    }


    //    }
    //}

    if(!found){
        //retval = "";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod);
    }
    

    return retval;
}
                


std::string ADD_REAL1_EXPR_REAL1_EXPR::toEvalString() const {
                        std::string retval = "";
                        bool found = false;
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalVelocityCoordinateVector.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinateVector.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinateVector.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinatePoint.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinatePoint.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
    }
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){
                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalVelocityCoordinateVector.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinateVector.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinateVector.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinatePoint.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinatePoint.fromalgebra ";
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")";
        
            }
        }
    }


    if (!found)
                                    {
                                        //ret = "";
                                        
    }
                                    std::replace(retval.begin(), retval.end(), '_', '.');
                                    std::size_t index;
                                    string sub_str = ": _";
                                    string singleperiod = ".a";
                                    while ((index = retval.find(": .")) != string::npos)
                                    {
                                        retval.replace(index, sub_str.length(), sub_str);
                                    }
                                    while ((index = retval.find(": ^")) != string::npos)
                                    {
                                        retval.replace(index, sub_str.length(), sub_str);
                                    }
                                    while ((index = retval.find("..")) != string::npos)
                                    {
                                        retval.replace(index, singleperiod.length(), singleperiod);
                                    }


                                    return retval;
                                }
                                

std::string ADD_REAL1_EXPR_REAL1_EXPR::toAlgebraString() const {
                        std::string retval = "";
                        bool found = false;

                        //  ret += "(";
                        //ret += "def var_" + std::to_string(++GLOBAL_INDEX) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalVelocityCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinatePointAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinatePointAlgebra " + this->toEvalString() + ")";
        
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalVelocityCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinatePointAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinatePointAlgebra " + this->toEvalString() + ")";
        
            }
        }
    }

    if(!found){
        //ret = "";
        
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod); 
    }
    
    
    return retval;
}
                

ADD_REAL1_EXPR_REAL1_EXPR::ADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject* d,interp::REAL1_EXPR * operand1,interp::REAL1_EXPR * operand2 ) : REAL1_EXPR(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string ADD_REAL1_EXPR_REAL1_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += " (lang.classicalVelocity.CoordinateVectorExpr.lit \n";
        retval += "(classicalVelocityCoordinateVector.fromalgebra ";
        retval += std::string("(classicalVelocityEval ") + "(lang.classicalVelocity.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalVelocityFrameEval ") + "(lang.classicalVelocity.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += " (lang.classicalTime.CoordinateVectorExpr.lit \n";
        retval += "(classicalTimeCoordinateVector.fromalgebra ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += " (lang.classicalGeometry.CoordinateVectorExpr.lit \n";
        retval += "(classicalGeometryCoordinateVector.fromalgebra ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += " (lang.classicalTime.CoordinatePointExpr.lit \n";
        retval += "(classicalTimeCoordinatePoint.fromalgebra ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< ADD_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<ADD_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += " (lang.classicalGeometry.CoordinatePointExpr.lit \n";
        retval += "(classicalGeometryCoordinatePoint.fromalgebra ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
    }
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){
                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
                retval += " (lang.classicalVelocity.CoordinateVectorExpr.lit \n";
        retval += "(classicalVelocityCoordinateVector.fromalgebra ";
        retval += std::string("(classicalVelocityEval ") + "(lang.classicalVelocity.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalVelocityFrameEval ") + "(lang.classicalVelocity.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
                retval += " (lang.classicalTime.CoordinateVectorExpr.lit \n";
        retval += "(classicalTimeCoordinateVector.fromalgebra ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
                retval += " (lang.classicalGeometry.CoordinateVectorExpr.lit \n";
        retval += "(classicalGeometryCoordinateVector.fromalgebra ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
                retval += " (lang.classicalTime.CoordinatePointExpr.lit \n";
        retval += "(classicalTimeCoordinatePoint.fromalgebra ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
                retval += " (lang.classicalGeometry.CoordinatePointExpr.lit \n";
        retval += "(classicalGeometryCoordinatePoint.fromalgebra ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
        retval += std::string("(") + this->operand_1->toAlgebraString() + "+ᵥ" + this->operand_2->toAlgebraString() + ")))";
        
            }
        }
    }


    //    }
    //}

    if(!found){
        //retval = "";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod);
    }
    

    return retval;
}
                


std::string REAL1_VAR_IDENT::toAlgebraString() const {
                        std::string retval = "";
                        bool found = false;

                        //  ret += "(";
                        //ret += "def var_" + std::to_string(++GLOBAL_INDEX) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalVelocityCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinatePointAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinatePointAlgebra " + this->toEvalString() + ")";
        
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalVelocityCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinatePointAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinatePointAlgebra " + this->toEvalString() + ")";
        
            }
        }
    }

    if(!found){
        //ret = "";
        
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod); 
    }
    
    
    return retval;
}
                

std::string REAL1_VAR_IDENT::toEvalString() const {
                        std::string retval = "";
                        bool found = false;

                        //  ret += "(";
                        //ret += "def var_" + std::to_string(++GLOBAL_INDEX) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalVelocityCoordinateVectorEval (lang.classicalVelocity.CoordinateVectorExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalTimeCoordinateVectorEval (lang.classicalTime.CoordinateVectorExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalGeometryCoordinateVectorEval (lang.classicalGeometry.CoordinateVectorExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalTimeCoordinatePointEval (lang.classicalTime.CoordinatePointExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalGeometryCoordinatePointEval (lang.classicalGeometry.CoordinatePointExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalVelocityCoordinateVectorEval (lang.classicalVelocity.CoordinateVectorExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalTimeCoordinateVectorEval (lang.classicalTime.CoordinateVectorExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalGeometryCoordinateVectorEval (lang.classicalGeometry.CoordinateVectorExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalTimeCoordinatePointEval (lang.classicalTime.CoordinatePointExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL1_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalGeometryCoordinatePointEval (lang.classicalGeometry.CoordinatePointExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
            }
        }
    }

    if(!found){
        //ret = "";
        
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod); 
    }
    
    
    return retval;
}
                

REAL1_VAR_IDENT::REAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* c, domain::DomainObject* d ) : Interp(c,d)
    {}

std::string REAL1_VAR_IDENT::toString() const {
                        std::string retval = "";
                        bool found = false;

                
                                int id = GLOBAL_IDS.count(const_cast < REAL1_VAR_IDENT *> (this)) ? GLOBAL_IDS[const_cast < REAL1_VAR_IDENT *> (this)] : GLOBAL_IDS[const_cast < REAL1_VAR_IDENT *> (this)] = (GLOBAL_INDEX += 2);
                                retval += "⟨⟨" + std::to_string(id) + "⟩⟩";
    
                                

    if (!found){
                        //ret = "";
                        
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {
        retval.replace(index, sub_str.length(), sub_str);
    }
    while ((index = retval.find(": ^")) != string::npos)
    {
        retval.replace(index, sub_str.length(), sub_str);
    }
    while ((index = retval.find("..")) != string::npos)
    {
        retval.replace(index, singleperiod.length(), singleperiod);
    }


                    return retval;
                }
                


std::string REAL3_VAR_IDENT::toAlgebraString() const {
                        std::string retval = "";
                        bool found = false;

                        //  ret += "(";
                        //ret += "def var_" + std::to_string(++GLOBAL_INDEX) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalVelocityCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinatePointAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinatePointAlgebra " + this->toEvalString() + ")";
        
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalVelocityCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinatePointAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinatePointAlgebra " + this->toEvalString() + ")";
        
            }
        }
    }

    if(!found){
        //ret = "";
        
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod); 
    }
    
    
    return retval;
}
                

std::string REAL3_VAR_IDENT::toEvalString() const {
                        std::string retval = "";
                        bool found = false;

                        //  ret += "(";
                        //ret += "def var_" + std::to_string(++GLOBAL_INDEX) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalVelocityCoordinateVectorEval (lang.classicalVelocity.CoordinateVectorExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalTimeCoordinateVectorEval (lang.classicalTime.CoordinateVectorExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalGeometryCoordinateVectorEval (lang.classicalGeometry.CoordinateVectorExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalTimeCoordinatePointEval (lang.classicalTime.CoordinatePointExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalGeometryCoordinatePointEval (lang.classicalGeometry.CoordinatePointExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalVelocityCoordinateVectorEval (lang.classicalVelocity.CoordinateVectorExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalTimeCoordinateVectorEval (lang.classicalTime.CoordinateVectorExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalGeometryCoordinateVectorEval (lang.classicalGeometry.CoordinateVectorExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalTimeCoordinatePointEval (lang.classicalTime.CoordinatePointExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_VAR_IDENT*>(this)) ? GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] : GLOBAL_IDS[const_cast<REAL3_VAR_IDENT*>(this)] = (GLOBAL_INDEX += 2); 
        return std::string("(classicalGeometryCoordinatePointEval (lang.classicalGeometry.CoordinatePointExpr.var ") + "⟨⟨" + std::to_string(id) +"⟩⟩) " + getLastEnv() + ")";
        
            }
        }
    }

    if(!found){
        //ret = "";
        
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod); 
    }
    
    
    return retval;
}
                

REAL3_VAR_IDENT::REAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* c, domain::DomainObject* d ) : Interp(c,d)
    {}

std::string REAL3_VAR_IDENT::toString() const {
                        std::string retval = "";
                        bool found = false;

                
                                int id = GLOBAL_IDS.count(const_cast < REAL3_VAR_IDENT *> (this)) ? GLOBAL_IDS[const_cast < REAL3_VAR_IDENT *> (this)] : GLOBAL_IDS[const_cast < REAL3_VAR_IDENT *> (this)] = (GLOBAL_INDEX += 2);
                                retval += "⟨⟨" + std::to_string(id) + "⟩⟩";
    
                                

    if (!found){
                        //ret = "";
                        
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {
        retval.replace(index, sub_str.length(), sub_str);
    }
    while ((index = retval.find(": ^")) != string::npos)
    {
        retval.replace(index, sub_str.length(), sub_str);
    }
    while ((index = retval.find("..")) != string::npos)
    {
        retval.replace(index, singleperiod.length(), singleperiod);
    }


                    return retval;
                }
                

REAL3_LITERAL::REAL3_LITERAL(coords::REAL3_LITERAL* c, domain::DomainObject* d) : REAL3_EXPR(c,d) {}
                    
std::string REAL3_LITERAL::toString() const {
    std::string retval = "";
    bool found = false;
    
    retval = "Calling toString on a production, rather than a case.";
    
    
    return retval;
}
                

std::string REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::toEvalString() const {
                        std::string retval = "";
                        bool found = false;
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalVelocityCoordinateVector.build ";
        retval += std::string("(classicalVelocityEval ") + "(lang.classicalVelocity.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalVelocityFrameEval ") + "(lang.classicalVelocity.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3)))";
        
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinateVector.build ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3)))";
        
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinateVector.build ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3)))";
        
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinatePoint.build ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3)))";
        
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinatePoint.build ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3)))";
        
    }
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){
                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalVelocityCoordinateVector.build ";
        retval += std::string("(classicalVelocityEval ") + "(lang.classicalVelocity.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalVelocityFrameEval ") + "(lang.classicalVelocity.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3))";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinateVector.build ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3))";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinateVector.build ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3))";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinatePoint.build ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3))";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinatePoint.build ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3))";
        
            }
        }
    }


    if (!found)
                                    {
                                        //ret = "";
                                        
    }
                                    std::replace(retval.begin(), retval.end(), '_', '.');
                                    std::size_t index;
                                    string sub_str = ": _";
                                    string singleperiod = ".a";
                                    while ((index = retval.find(": .")) != string::npos)
                                    {
                                        retval.replace(index, sub_str.length(), sub_str);
                                    }
                                    while ((index = retval.find(": ^")) != string::npos)
                                    {
                                        retval.replace(index, sub_str.length(), sub_str);
                                    }
                                    while ((index = retval.find("..")) != string::npos)
                                    {
                                        retval.replace(index, singleperiod.length(), singleperiod);
                                    }


                                    return retval;
                                }
                                

std::string REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::toAlgebraString() const {
                        std::string retval = "";
                        bool found = false;

                        //  ret += "(";
                        //ret += "def var_" + std::to_string(++GLOBAL_INDEX) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalVelocityCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinatePointAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinatePointAlgebra " + this->toEvalString() + ")";
        
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalVelocityCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinatePointAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] : GLOBAL_IDS[const_cast<REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinatePointAlgebra " + this->toEvalString() + ")";
        
            }
        }
    }

    if(!found){
        //ret = "";
        
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod); 
    }
    
    
    return retval;
}
                

REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject* d,interp::REAL1_EXPR * operand1,interp::REAL1_EXPR * operand2,interp::REAL1_EXPR * operand3 ) : REAL3_LITERAL(c,d)
   ,operand_1(operand1),operand_2(operand2),operand_3(operand3) {}

std::string REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
    //    }
    //}

    if(!found){
        //retval = "";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod);
    }
    

    return retval;
}
                


std::string REAL3_EMPTY::toEvalString() const {
                        std::string retval = "";
                        bool found = false;
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL3_EMPTY*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] : GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalVelocityCoordinateVector.build ";
        retval += std::string("(classicalVelocityEval ") + "(lang.classicalVelocity.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalVelocityFrameEval ") + "(lang.classicalVelocity.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3)))";
        
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL3_EMPTY*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] : GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinateVector.build ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3)))";
        
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL3_EMPTY*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] : GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinateVector.build ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3)))";
        
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL3_EMPTY*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] : GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinatePoint.build ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3)))";
        
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL3_EMPTY*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] : GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinatePoint.build ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3)))";
        
    }
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){
                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalVelocityCoordinateVector.build ";
        retval += std::string("(classicalVelocityEval ") + "(lang.classicalVelocity.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalVelocityFrameEval ") + "(lang.classicalVelocity.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3))";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinateVector.build ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3))";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinateVector.build ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3))";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinatePoint.build ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3))";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL3_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL3_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinatePoint.build ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 3; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 3))";
        
            }
        }
    }


    if (!found)
                                    {
                                        //ret = "";
                                        
    }
                                    std::replace(retval.begin(), retval.end(), '_', '.');
                                    std::size_t index;
                                    string sub_str = ": _";
                                    string singleperiod = ".a";
                                    while ((index = retval.find(": .")) != string::npos)
                                    {
                                        retval.replace(index, sub_str.length(), sub_str);
                                    }
                                    while ((index = retval.find(": ^")) != string::npos)
                                    {
                                        retval.replace(index, sub_str.length(), sub_str);
                                    }
                                    while ((index = retval.find("..")) != string::npos)
                                    {
                                        retval.replace(index, singleperiod.length(), singleperiod);
                                    }


                                    return retval;
                                }
                                

std::string REAL3_EMPTY::toAlgebraString() const {
                        std::string retval = "";
                        bool found = false;

                        //  ret += "(";
                        //ret += "def var_" + std::to_string(++GLOBAL_INDEX) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_EMPTY*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] : GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalVelocityCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_EMPTY*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] : GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_EMPTY*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] : GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_EMPTY*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] : GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinatePointAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_EMPTY*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] : GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinatePointAlgebra " + this->toEvalString() + ")";
        
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_EMPTY*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] : GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalVelocityCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_EMPTY*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] : GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_EMPTY*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] : GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_EMPTY*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] : GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinatePointAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,3>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL3_EMPTY*>(this)) ? GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] : GLOBAL_IDS[const_cast<REAL3_EMPTY*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinatePointAlgebra " + this->toEvalString() + ")";
        
            }
        }
    }

    if(!found){
        //ret = "";
        
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod); 
    }
    
    
    return retval;
}
                

REAL3_EMPTY::REAL3_EMPTY(coords::REAL3_EMPTY* c, domain::DomainObject* d ) : REAL3_LITERAL(c,d)
    {}

std::string REAL3_EMPTY::toString() const {
    bool found = false;
    std::string retval = "";
    //    }
    //}

    if(!found){
        //retval = "";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod);
    }
    

    return retval;
}
                

REAL1_LITERAL::REAL1_LITERAL(coords::REAL1_LITERAL* c, domain::DomainObject* d) : REAL1_EXPR(c,d) {}
                    
std::string REAL1_LITERAL::toString() const {
    std::string retval = "";
    bool found = false;
    
    retval = "Calling toString on a production, rather than a case.";
    
    
    return retval;
}
                

std::string REAL1_LIT::toEvalString() const {
                        std::string retval = "";
                        bool found = false;
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalVelocityCoordinateVector.build ";
        retval += std::string("(classicalVelocityEval ") + "(lang.classicalVelocity.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalVelocityFrameEval ") + "(lang.classicalVelocity.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1)))";
        
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinateVector.build ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1)))";
        
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinateVector.build ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1)))";
        
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinatePoint.build ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1)))";
        
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinatePoint.build ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1)))";
        
    }
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){
                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalVelocityCoordinateVector.build ";
        retval += std::string("(classicalVelocityEval ") + "(lang.classicalVelocity.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalVelocityFrameEval ") + "(lang.classicalVelocity.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1))";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinateVector.build ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1))";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinateVector.build ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1))";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalTimeCoordinatePoint.build ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1))";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += "(classicalGeometryCoordinatePoint.build ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1))";
        
            }
        }
    }


    if (!found)
                                    {
                                        //ret = "";
                                        
    }
                                    std::replace(retval.begin(), retval.end(), '_', '.');
                                    std::size_t index;
                                    string sub_str = ": _";
                                    string singleperiod = ".a";
                                    while ((index = retval.find(": .")) != string::npos)
                                    {
                                        retval.replace(index, sub_str.length(), sub_str);
                                    }
                                    while ((index = retval.find(": ^")) != string::npos)
                                    {
                                        retval.replace(index, sub_str.length(), sub_str);
                                    }
                                    while ((index = retval.find("..")) != string::npos)
                                    {
                                        retval.replace(index, singleperiod.length(), singleperiod);
                                    }


                                    return retval;
                                }
                                

std::string REAL1_LIT::toAlgebraString() const {
                        std::string retval = "";
                        bool found = false;

                        //  ret += "(";
                        //ret += "def var_" + std::to_string(++GLOBAL_INDEX) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalVelocityCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinatePointAlgebra " + this->toEvalString() + ")";
        
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinatePointAlgebra " + this->toEvalString() + ")";
        
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalVelocityCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinateVectorAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalTimeCoordinatePointAlgebra " + this->toEvalString() + ")";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(cont->getValue())){
                found = true;
        auto env = getLastEnv();
        int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        return "(classicalGeometryCoordinatePointAlgebra " + this->toEvalString() + ")";
        
            }
        }
    }

    if(!found){
        //ret = "";
        
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod); 
    }
    
    
    return retval;
}
                

REAL1_LIT::REAL1_LIT(coords::REAL1_LIT* c, domain::DomainObject* d ) : REAL1_LITERAL(c,d)
    {}

std::string REAL1_LIT::toString() const {
    bool found = false;
    std::string retval = "";
    if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += " (lang.classicalVelocity.CoordinateVectorExpr.lit \n";
        retval += "(classicalVelocityCoordinateVector.build ";
        retval += std::string("(classicalVelocityEval ") + "(lang.classicalVelocity.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalVelocityFrameEval ") + "(lang.classicalVelocity.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1)))";
        
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += " (lang.classicalTime.CoordinateVectorExpr.lit \n";
        retval += "(classicalTimeCoordinateVector.build ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1)))";
        
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += " (lang.classicalGeometry.CoordinateVectorExpr.lit \n";
        retval += "(classicalGeometryCoordinateVector.build ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1)))";
        
    }
    if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += " (lang.classicalTime.CoordinatePointExpr.lit \n";
        retval += "(classicalTimeCoordinatePoint.build ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1)))";
        
    }
    if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(this->dom_)){
        found = true;
        //auto env = getEnvName();
        //int id = GLOBAL_IDS.count(const_cast< REAL1_LIT*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] : GLOBAL_IDS[const_cast<REAL1_LIT*>(this)] = (GLOBAL_INDEX += 2); 
        auto interpSp = i2d_->getSpace(dc->getSpace());
        int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
        auto interpFr = i2d_->getFrame(dc->getFrame());
		int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
        retval += " (lang.classicalGeometry.CoordinatePointExpr.lit \n";
        retval += "(classicalGeometryCoordinatePoint.build ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1)))";
        
    }
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){
                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocityCoordinateVector<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
                retval += " (lang.classicalVelocity.CoordinateVectorExpr.lit \n";
        retval += "(classicalVelocityCoordinateVector.build ";
        retval += std::string("(classicalVelocityEval ") + "(lang.classicalVelocity.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalVelocityFrameEval ") + "(lang.classicalVelocity.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1)))";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinateVector<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
                retval += " (lang.classicalTime.CoordinateVectorExpr.lit \n";
        retval += "(classicalTimeCoordinateVector.build ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1)))";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinateVector<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
                retval += " (lang.classicalGeometry.CoordinateVectorExpr.lit \n";
        retval += "(classicalGeometryCoordinateVector.build ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1)))";
        
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeCoordinatePoint<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
                retval += " (lang.classicalTime.CoordinatePointExpr.lit \n";
        retval += "(classicalTimeCoordinatePoint.build ";
        retval += std::string("(classicalTimeEval ") + "(lang.classicalTime.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalTimeFrameEval ") + "(lang.classicalTime.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1)))";
        
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometryCoordinatePoint<float,1>*>(cont->getValue())){
                //auto env = getEnvName();
                //int id = GLOBAL_IDS.count(const_cast< REAL1_LITERAL*>(this)) ? GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] : GLOBAL_IDS[const_cast<REAL1_LITERAL*>(this)] = (GLOBAL_INDEX += 2); 
                auto interpSp = i2d_->getSpace(dc->getSpace());
                int sid = GLOBAL_IDS.count(const_cast<Space*>(interpSp)) ? GLOBAL_IDS[const_cast<Space*>(interpSp)] : GLOBAL_IDS[const_cast<Space*>(interpSp)] = (GLOBAL_INDEX += 2); 
                auto interpFr = i2d_->getFrame(dc->getFrame());
int fid = GLOBAL_IDS.count(const_cast<Frame*>(interpFr)) ? GLOBAL_IDS[const_cast<Frame*>(interpFr)] : GLOBAL_IDS[const_cast<Frame*>(interpFr)] = (GLOBAL_INDEX += 2);
                retval += " (lang.classicalGeometry.CoordinatePointExpr.lit \n";
        retval += "(classicalGeometryCoordinatePoint.build ";
        retval += std::string("(classicalGeometryEval ") + "(lang.classicalGeometry.spaceExpr.var ⟨⟨" + std::to_string(sid) + "⟩⟩) " + getLastEnv() + ")\n";
        retval += std::string("(classicalGeometryFrameEval ") + "(lang.classicalGeometry.frameExpr.var ⟨⟨" + std::to_string(fid) + "⟩⟩) " + getLastEnv() + ")\n"; 
            retval += "(⟨[]";
        for (auto i = 0; i < 1; i++)
            retval += "++[" + std::to_string(*dc->getValue(i)) + "]";
        retval += "\n\t\t,by refl⟩ : vector ℝ 1)))";
        
            }
        }
    }


    //    }
    //}

    if(!found){
        //retval = "";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    std::size_t index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    
        retval.replace(index, sub_str.length(), sub_str); 
    }
    while ((index = retval.find("..")) != string::npos)
    {    
        retval.replace(index, singleperiod.length(), singleperiod);
    }
    

    return retval;
}
                
} // namespace coords