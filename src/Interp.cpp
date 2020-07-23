#include "Interp.h"

#include "Domain.h"

#include <g3log/g3log.hpp>

#include <algorithm>

using namespace g3; 

namespace interp{

int GLOBAL_INDEX = 0;

Interp::Interp(coords::Coords* c, domain::DomainObject* d) : coords_(c), dom_(d){
}

std::string Space::toString() const {
    std::string retval = "";
    bool found = false;

	if(auto dc = dynamic_cast<domain::EuclideanGeometry*>(s_)){
        found = true;
        retval += "def " + dc->getName() + "var : EuclideanGeometry3SpaceVar := (!" + std::to_string(++GLOBAL_INDEX) + ")" + "\n";
        retval += "def " + dc->getName() + "sp := (EuclideanGeometry" + std::to_string(dc->getDimension()) +  "SpaceExpression.EuclideanGeometry" + std::to_string(dc->getDimension()) +  "Literal ( BuildEuclideanGeometrySpace \"" + dc->getName() + "\" " + std::to_string(dc->getDimension()) +  "))\n";; 
        retval += "def " + dc->getName() + " := PhysGlobalCommand.GlobalSpace (⊢" + dc->getName() + "var) (⊢" + dc->getName() + "sp)\n";
    }
	if(auto dc = dynamic_cast<domain::ClassicalTime*>(s_)){
        found = true;
        retval += "def " + dc->getName() + "var : ClassicalTimeSpaceVar := (!" + std::to_string(++GLOBAL_INDEX) + ")" + "\n";
        retval += "def " + dc->getName() + "sp :=  (ClassicalTimeSpaceExpression.ClassicalTimeLiteral ( BuildClassicalTimeSpace \"" + dc->getName() + "\" ))\n";; 
        retval += "def " + dc->getName() + " := PhysGlobalCommand.GlobalSpace (⊢" + dc->getName() + "var) (⊢" + dc->getName() + "sp)\n";
    }
	if(auto dc = dynamic_cast<domain::ClassicalVelocity*>(s_)){
        found = true;
        retval += "def " + dc->getName() + "var : ClassicalVelocity3SpaceVar := (!" + std::to_string(++GLOBAL_INDEX) + ")" + "\n";
        retval += "def " + dc->getName() + "sp := (ClassicalVelocity" + std::to_string(dc->getDimension()) +  "SpaceExpression.ClassicalVelocity" + std::to_string(dc->getDimension()) +  "Literal ( BuildClassicalVelocitySpace \"" + dc->getName() + "\" " + std::to_string(dc->getDimension()) +  "))\n";; 
        retval += "def " + dc->getName() + " := PhysGlobalCommand.GlobalSpace (⊢" + dc->getName() + "var) (⊢" + dc->getName() + "sp)\n";
    }

    if(!found){
        //retval = "--Unknown space type - Translation Failed!";
    }

    return retval;
};

std::string Frame::toString() const {
    std::string retval = "";
    bool found = false;
    bool isStandard = this->f_->getName() == "Standard";
    if(!isStandard)
        return retval;

	if(auto dc = dynamic_cast<domain::EuclideanGeometry*>(f_->getSpace())){
        found = true;
        retval += "def " +dc->getName()+"."+f_->getName() + "var : EuclideanGeometry3FrameVar := (!" + std::to_string(++GLOBAL_INDEX) + ")" + "\n";
        if(!isStandard){
            retval += "def " + dc->getName()+"."+f_->getName() + "fr := EuclideanGeometry3FrameExpression.FrameLiteral ( BuildEuclideanGeometryFrame "+ dc->getName()+"))";
        }
        else{
            retval += "def " + dc->getName()+"."+f_->getName() + "fr := EuclideanGeometry3FrameExpression.FrameLiteral ( GetEuclideanGeometryStandardFrame (EvalEuclideanGeometry3SpaceExpression " + dc->getName()+"sp))\n";
    
        }
        retval += "def " + dc->getName()+"."+f_->getName() + " := PhysGlobalCommand.GlobalFrame (⊢" + dc->getName()+"."+f_->getName() + "var) (⊢" + dc->getName()+"."+f_->getName() + "fr)\n";
    }
	if(auto dc = dynamic_cast<domain::ClassicalTime*>(f_->getSpace())){
        found = true;
        retval += "def " +dc->getName()+"."+f_->getName() + "var : ClassicalTimeFrameVar := (!" + std::to_string(++GLOBAL_INDEX) + ")" + "\n";
        if(!isStandard){
            retval += "def " + dc->getName()+"."+f_->getName() + "fr := ClassicalTimeFrameExpression.FrameLiteral ( BuildClassicalTimeFrame "+ dc->getName()+"))";
        }
        else{
            retval += "def " + dc->getName()+"."+f_->getName() + "fr := ClassicalTimeFrameExpression.FrameLiteral ( GetClassicalTimeStandardFrame (EvalClassicalTimeSpaceExpression " + dc->getName()+"sp))\n";
    
        }
        retval += "def " + dc->getName()+"."+f_->getName() + " := PhysGlobalCommand.GlobalFrame (⊢" + dc->getName()+"."+f_->getName() + "var) (⊢" + dc->getName()+"."+f_->getName() + "fr)\n";
    }
	if(auto dc = dynamic_cast<domain::ClassicalVelocity*>(f_->getSpace())){
        found = true;
        retval += "def " +dc->getName()+"."+f_->getName() + "var : ClassicalVelocity3FrameVar := (!" + std::to_string(++GLOBAL_INDEX) + ")" + "\n";
        if(!isStandard){
            retval += "def " + dc->getName()+"."+f_->getName() + "fr := ClassicalVelocity3FrameExpression.FrameLiteral ( BuildClassicalVelocityFrame "+ dc->getName()+"))";
        }
        else{
            retval += "def " + dc->getName()+"."+f_->getName() + "fr := ClassicalVelocity3FrameExpression.FrameLiteral ( GetClassicalVelocityStandardFrame (EvalClassicalVelocity3SpaceExpression " + dc->getName()+"sp))\n";
    
        }
        retval += "def " + dc->getName()+"."+f_->getName() + " := PhysGlobalCommand.GlobalFrame (⊢" + dc->getName()+"."+f_->getName() + "var) (⊢" + dc->getName()+"."+f_->getName() + "fr)\n";
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
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //ret = "";
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
    cmdval = "\ndef " + this->coords_->toString() + "globalseq : PhysGlobalCommand := PhysGlobalCommand.Seq " + cmdval;


    cmdval += "\ndef " + this->coords_->toString() + " : PhysProgram := PhysProgram.Program " + this->coords_->toString() + "globalseq";


    retval += "\n" + cmdval + "\n";
    

    //std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
std::string SEQ_GLOBALSTMT::toStringLinked(std::vector<interp::Space*> links, std::vector<std::string> names, std::vector<interp::Frame*> framelinks, std::vector<string> framenames, bool before) { 
    //std::string toStr = this->toString();
    std::string retval = "";
        string cmdvalstart = "::[]";
        string cmdval = "";
    int i = 0;
    if(before)
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

    }
    cmdval += ""; 
    cmdval = "\ndef " + this->coords_->toString() + "globalseq : PhysGlobalCommand := PhysGlobalCommand.Seq (" + cmdval + cmdvalstart + ")";


    cmdval += "\ndef " + this->coords_->toString() + " : PhysProgram := PhysProgram.Program " + this->coords_->toString() + "globalseq";


    retval += "\n" + cmdval + "\n";
    

    //std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //ret = "";
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

MAIN_STMT::MAIN_STMT(coords::MAIN_STMT* c, domain::DomainObject* d,interp::STMT * operand1 ) : GLOBALSTMT(c,d)
   ,operand_1(operand1) {}

std::string MAIN_STMT::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::GLOBALSTMT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : PhysGlobalCommand := PhysGlobalCommand.Main " + operand_1->coords_->toString();

    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


FUNCTION_STMT::FUNCTION_STMT(coords::FUNCTION_STMT* c, domain::DomainObject* d,interp::STMT * operand1 ) : GLOBALSTMT(c,d)
   ,operand_1(operand1) {}

std::string FUNCTION_STMT::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::GLOBALSTMT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : PhysGlobalCommand := PhysGlobalCommand.Function " + operand_1->coords_->toString();

    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

STMT::STMT(coords::STMT* c, domain::DomainObject* d) : Interp(c,d) {}
                    
std::string STMT::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //ret = "";
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
    cmdval = "\ndef " + this->coords_->toString() + " : PhysCommand := PhysCommand.Seq " + cmdval;


    retval += "\n" + cmdval + "\n";
    

    //std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
std::string COMPOUND_STMT::toStringLinked(std::vector<interp::Space*> links, std::vector<std::string> names, std::vector<interp::Frame*> framelinks, std::vector<string> framenames, bool before) { 
    //std::string toStr = this->toString();
    std::string retval = "";
        string cmdvalstart = "::[]";
        string cmdval = "";
    int i = 0;
    if(before)
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

    }
    cmdval += ""; 
    cmdval = "\ndef " + this->coords_->toString() + " : PhysCommand := PhysCommand.Seq " + cmdval;


    retval += "\n" + cmdval + "\n";
    

    //std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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


IFCOND::IFCOND(coords::IFCOND* c, domain::DomainObject* d) : STMT(c,d) {}
                    
std::string IFCOND::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //ret = "";
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

IFTHEN_EXPR_STMT::IFTHEN_EXPR_STMT(coords::IFTHEN_EXPR_STMT* c, domain::DomainObject* d,interp::EXPR * operand1,interp::STMT * operand2 ) : IFCOND(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string IFTHEN_EXPR_STMT::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //retval = "";
        "Not implemented";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


IFTHENELSEIF_EXPR_STMT_IFCOND::IFTHENELSEIF_EXPR_STMT_IFCOND(coords::IFTHENELSEIF_EXPR_STMT_IFCOND* c, domain::DomainObject* d,interp::EXPR * operand1,interp::STMT * operand2,interp::IFCOND * operand3 ) : IFCOND(c,d)
   ,operand_1(operand1),operand_2(operand2),operand_3(operand3) {}

std::string IFTHENELSEIF_EXPR_STMT_IFCOND::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
	retval += "\n"+ operand_3->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //retval = "";
        "Not implemented";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


IFTHENELSE_EXPR_STMT_STMT::IFTHENELSE_EXPR_STMT_STMT(coords::IFTHENELSE_EXPR_STMT_STMT* c, domain::DomainObject* d,interp::EXPR * operand1,interp::STMT * operand2,interp::STMT * operand3 ) : IFCOND(c,d)
   ,operand_1(operand1),operand_2(operand2),operand_3(operand3) {}

std::string IFTHENELSE_EXPR_STMT_STMT::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
	retval += "\n"+ operand_3->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //retval = "";
        "Not implemented";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

EXPR::EXPR(coords::EXPR* c, domain::DomainObject* d) : STMT(c,d) {}
                    
std::string EXPR::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //ret = "";
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                
ASSIGNMENT::ASSIGNMENT(coords::ASSIGNMENT* c, domain::DomainObject* d) : STMT(c,d) {}
                    
std::string ASSIGNMENT::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //ret = "";
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

ASSIGN_REAL1_VAR_REAL1_EXPR::ASSIGN_REAL1_VAR_REAL1_EXPR(coords::ASSIGN_REAL1_VAR_REAL1_EXPR* c, domain::DomainObject* d,interp::REAL1_VAR_IDENT * operand1,interp::REAL1_EXPR * operand2 ) : ASSIGNMENT(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string ASSIGN_REAL1_VAR_REAL1_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::STMT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + + "(⊢("+this->operand_1->coords_->toString()+"))=(⊢("+this->operand_2->coords_->toString()+"))";;
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


ASSIGN_REAL3_VAR_REAL3_EXPR::ASSIGN_REAL3_VAR_REAL3_EXPR(coords::ASSIGN_REAL3_VAR_REAL3_EXPR* c, domain::DomainObject* d,interp::REAL3_VAR_IDENT * operand1,interp::REAL3_EXPR * operand2 ) : ASSIGNMENT(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string ASSIGN_REAL3_VAR_REAL3_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::STMT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + + "(⊢("+this->operand_1->coords_->toString()+"))=(⊢("+this->operand_2->coords_->toString()+"))";;
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


ASSIGN_REAL4_VAR_REAL4_EXPR::ASSIGN_REAL4_VAR_REAL4_EXPR(coords::ASSIGN_REAL4_VAR_REAL4_EXPR* c, domain::DomainObject* d,interp::REAL4_VAR_IDENT * operand1,interp::REAL4_EXPR * operand2 ) : ASSIGNMENT(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string ASSIGN_REAL4_VAR_REAL4_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::STMT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + + "(⊢("+this->operand_1->coords_->toString()+"))=(⊢("+this->operand_2->coords_->toString()+"))";;
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* c, domain::DomainObject* d,interp::REALMATRIX_VAR_IDENT * operand1,interp::REALMATRIX_EXPR * operand2 ) : ASSIGNMENT(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::STMT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + + "(⊢("+this->operand_1->coords_->toString()+"))=(⊢("+this->operand_2->coords_->toString()+"))";;
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //ret = "";
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

DECL_REAL1_VAR_REAL1_EXPR::DECL_REAL1_VAR_REAL1_EXPR(coords::DECL_REAL1_VAR_REAL1_EXPR* c, domain::DomainObject* d,interp::REAL1_VAR_IDENT * operand1,interp::REAL1_EXPR * operand2 ) : DECLARE(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string DECL_REAL1_VAR_REAL1_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::STMT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + + "(⊢("+this->operand_1->coords_->toString()+"))=(⊢("+this->operand_2->coords_->toString()+"))";;
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::STMT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + + "(⊢("+this->operand_1->coords_->toString()+"))=(⊢("+this->operand_2->coords_->toString()+"))";;
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


DECL_REAL4_VAR_REAL4_EXPR::DECL_REAL4_VAR_REAL4_EXPR(coords::DECL_REAL4_VAR_REAL4_EXPR* c, domain::DomainObject* d,interp::REAL4_VAR_IDENT * operand1,interp::REAL4_EXPR * operand2 ) : DECLARE(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string DECL_REAL4_VAR_REAL4_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::STMT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + + "(⊢("+this->operand_1->coords_->toString()+"))=(⊢("+this->operand_2->coords_->toString()+"))";;
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


DECL_REALMATRIX_VAR_REALMATRIX_EXPR::DECL_REALMATRIX_VAR_REALMATRIX_EXPR(coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* c, domain::DomainObject* d,interp::REALMATRIX_VAR_IDENT * operand1,interp::REALMATRIX_EXPR * operand2 ) : DECLARE(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string DECL_REALMATRIX_VAR_REALMATRIX_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::STMT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + + "(⊢("+this->operand_1->coords_->toString()+"))=(⊢("+this->operand_2->coords_->toString()+"))";;
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
	retval += "\n"+ operand_1->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //retval = "";
        "Not implemented";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
	retval += "\n"+ operand_1->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //retval = "";
        "Not implemented";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


DECL_REAL4_VAR::DECL_REAL4_VAR(coords::DECL_REAL4_VAR* c, domain::DomainObject* d,interp::REAL4_VAR_IDENT * operand1 ) : DECLARE(c,d)
   ,operand_1(operand1) {}

std::string DECL_REAL4_VAR::toString() const {
    bool found = false;
    std::string retval = "";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //retval = "";
        "Not implemented";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


DECL_REALMATRIX_VAR::DECL_REALMATRIX_VAR(coords::DECL_REALMATRIX_VAR* c, domain::DomainObject* d,interp::REALMATRIX_VAR_IDENT * operand1 ) : DECLARE(c,d)
   ,operand_1(operand1) {}

std::string DECL_REALMATRIX_VAR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //retval = "";
        "Not implemented";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

REAL1_EXPR::REAL1_EXPR(coords::REAL1_EXPR* c, domain::DomainObject* d) : EXPR(c,d) {}
                    
std::string REAL1_EXPR::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
        }
    }

    if(!found){
        //ret = "";
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

PAREN_REAL1_EXPR::PAREN_REAL1_EXPR(coords::PAREN_REAL1_EXPR* c, domain::DomainObject* d,interp::REAL1_EXPR * operand1 ) : REAL1_EXPR(c,d)
   ,operand_1(operand1) {}

std::string PAREN_REAL1_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "$" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


INV_REAL1_EXPR::INV_REAL1_EXPR(coords::INV_REAL1_EXPR* c, domain::DomainObject* d,interp::REAL1_EXPR * operand1 ) : REAL1_EXPR(c,d)
   ,operand_1(operand1) {}

std::string INV_REAL1_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + " (" + operand_1->coords_->toString() + ") + " + "⁻¹";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


NEG_REAL1_EXPR::NEG_REAL1_EXPR(coords::NEG_REAL1_EXPR* c, domain::DomainObject* d,interp::REAL1_EXPR * operand1 ) : REAL1_EXPR(c,d)
   ,operand_1(operand1) {}

std::string NEG_REAL1_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "-" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "+" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "+" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "+" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "+" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "+" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "+" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "+" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "+" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "(" + operand_1->coords_->toString() + ")"+ "+" +"(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


SUB_REAL1_EXPR_REAL1_EXPR::SUB_REAL1_EXPR_REAL1_EXPR(coords::SUB_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject* d,interp::REAL1_EXPR * operand1,interp::REAL1_EXPR * operand2 ) : REAL1_EXPR(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string SUB_REAL1_EXPR_REAL1_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "(" + operand_1->coords_->toString() + ")"+ "-" +"(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


MUL_REAL1_EXPR_REAL1_EXPR::MUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject* d,interp::REAL1_EXPR * operand1,interp::REAL1_EXPR * operand2 ) : REAL1_EXPR(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string MUL_REAL1_EXPR_REAL1_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "(" + operand_1->coords_->toString() + ")"+ "⬝" +"(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


DIV_REAL1_EXPR_REAL1_EXPR::DIV_REAL1_EXPR_REAL1_EXPR(coords::DIV_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject* d,interp::REAL1_EXPR * operand1,interp::REAL1_EXPR * operand2 ) : REAL1_EXPR(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string DIV_REAL1_EXPR_REAL1_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "(" + operand_1->coords_->toString() + ")"+ "/" +"(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "%" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

REAL3_EXPR::REAL3_EXPR(coords::REAL3_EXPR* c, domain::DomainObject* d) : EXPR(c,d) {}
                    
std::string REAL3_EXPR::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
        }
    }

    if(!found){
        //ret = "";
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

PAREN_REAL3_EXPR::PAREN_REAL3_EXPR(coords::PAREN_REAL3_EXPR* c, domain::DomainObject* d,interp::REAL3_EXPR * operand1 ) : REAL3_EXPR(c,d)
   ,operand_1(operand1) {}

std::string PAREN_REAL3_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "$" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " +" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + " +" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + " +" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + " +" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + " +" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + " +" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + " +" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " +" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + " +" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + " +" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + " +" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + " +" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + " +" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + " +" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "+" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


SUB_REAL3_EXPR_REAL3_EXPR::SUB_REAL3_EXPR_REAL3_EXPR(coords::SUB_REAL3_EXPR_REAL3_EXPR* c, domain::DomainObject* d,interp::REAL3_EXPR * operand1,interp::REAL3_EXPR * operand2 ) : REAL3_EXPR(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string SUB_REAL3_EXPR_REAL3_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "-" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "(" + operand_1->coords_->toString() + ")"+ "-" +"(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


INV_REAL3_EXPR::INV_REAL3_EXPR(coords::INV_REAL3_EXPR* c, domain::DomainObject* d,interp::REAL3_EXPR * operand1 ) : REAL3_EXPR(c,d)
   ,operand_1(operand1) {}

std::string INV_REAL3_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + " (" + operand_1->coords_->toString() + ") + " + "⁻¹";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


NEG_REAL3_EXPR::NEG_REAL3_EXPR(coords::NEG_REAL3_EXPR* c, domain::DomainObject* d,interp::REAL3_EXPR * operand1 ) : REAL3_EXPR(c,d)
   ,operand_1(operand1) {}

std::string NEG_REAL3_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + " -" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "-" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


MUL_REAL3_EXPR_REAL1_EXPR::MUL_REAL3_EXPR_REAL1_EXPR(coords::MUL_REAL3_EXPR_REAL1_EXPR* c, domain::DomainObject* d,interp::REAL3_EXPR * operand1,interp::REAL1_EXPR * operand2 ) : REAL3_EXPR(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string MUL_REAL3_EXPR_REAL1_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "(" + operand_1->coords_->toString() + ")"+ "⬝" +"(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


MUL_REALMATRIX_EXPR_REAL3_EXPR::MUL_REALMATRIX_EXPR_REAL3_EXPR(coords::MUL_REALMATRIX_EXPR_REAL3_EXPR* c, domain::DomainObject* d,interp::REALMATRIX_EXPR * operand1,interp::REAL3_EXPR * operand2 ) : REAL3_EXPR(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string MUL_REALMATRIX_EXPR_REAL3_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "(" + operand_1->coords_->toString() + ")"+ "⬝" +"(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


DIV_REAL3_EXPR_REAL1_EXPR::DIV_REAL3_EXPR_REAL1_EXPR(coords::DIV_REAL3_EXPR_REAL1_EXPR* c, domain::DomainObject* d,interp::REAL3_EXPR * operand1,interp::REAL1_EXPR * operand2 ) : REAL3_EXPR(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string DIV_REAL3_EXPR_REAL1_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "/" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "(" + operand_1->coords_->toString() + ")"+ "/" +"(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "%" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

REAL4_EXPR::REAL4_EXPR(coords::REAL4_EXPR* c, domain::DomainObject* d) : EXPR(c,d) {}
                    
std::string REAL4_EXPR::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeHomogenousPoint*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3HomogenousPoint*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeHomogenousPoint*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3HomogenousPoint*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
        }
    }

    if(!found){
        //ret = "";
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

PAREN_REAL4_EXPR::PAREN_REAL4_EXPR(coords::PAREN_REAL4_EXPR* c, domain::DomainObject* d,interp::REAL4_EXPR * operand1 ) : REAL4_EXPR(c,d)
   ,operand_1(operand1) {}

std::string PAREN_REAL4_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeHomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeHomogenousPointExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3HomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3HomogenousPointExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeHomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeHomogenousPointExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3HomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3HomogenousPointExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "$" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


ADD_REAL4_EXPR_REAL4_EXPR::ADD_REAL4_EXPR_REAL4_EXPR(coords::ADD_REAL4_EXPR_REAL4_EXPR* c, domain::DomainObject* d,interp::REAL4_EXPR * operand1,interp::REAL4_EXPR * operand2 ) : REAL4_EXPR(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string ADD_REAL4_EXPR_REAL4_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "+" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "+" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeHomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeHomogenousPointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "+" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3HomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3HomogenousPointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "+" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "+" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "+" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeHomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeHomogenousPointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "+" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3HomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3HomogenousPointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "+" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "(" + operand_1->coords_->toString() + ")"+ "+" +"(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


MUL_REAL4_EXPR_REAL1_EXPR::MUL_REAL4_EXPR_REAL1_EXPR(coords::MUL_REAL4_EXPR_REAL1_EXPR* c, domain::DomainObject* d,interp::REAL4_EXPR * operand1,interp::REAL1_EXPR * operand2 ) : REAL4_EXPR(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string MUL_REAL4_EXPR_REAL1_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeHomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeHomogenousPointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3HomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3HomogenousPointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeHomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeHomogenousPointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3HomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3HomogenousPointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "(" + operand_1->coords_->toString() + ")"+ "⬝" +"(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


REF_REAL4_VAR::REF_REAL4_VAR(coords::REF_REAL4_VAR* c, domain::DomainObject* d,interp::REAL4_VAR_IDENT * operand1 ) : REAL4_EXPR(c,d)
   ,operand_1(operand1) {}

std::string REF_REAL4_VAR::toString() const {
    bool found = false;
    std::string retval = "";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeHomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeHomogenousPointExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3HomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3HomogenousPointExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeHomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeHomogenousPointExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3HomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3HomogenousPointExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "%" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

REALMATRIX_EXPR::REALMATRIX_EXPR(coords::REALMATRIX_EXPR* c, domain::DomainObject* d) : EXPR(c,d) {}
                    
std::string REALMATRIX_EXPR::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scaling*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScaling*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scaling*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Shear*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeShear*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Shear*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3BasisChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeBasisChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3BasisChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeFrameChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3FrameChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scaling*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScaling*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scaling*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Shear*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeShear*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Shear*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3BasisChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeBasisChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3BasisChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeFrameChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3FrameChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
        }
    }

    if(!found){
        //ret = "";
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

PAREN_REALMATRIX_EXPR::PAREN_REALMATRIX_EXPR(coords::PAREN_REALMATRIX_EXPR* c, domain::DomainObject* d,interp::REALMATRIX_EXPR * operand1 ) : REALMATRIX_EXPR(c,d)
   ,operand_1(operand1) {}

std::string PAREN_REALMATRIX_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalingExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalingExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalingExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ShearExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeShear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeShearExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ShearExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3BasisChangeExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeBasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeBasisChangeExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3BasisChangeExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeFrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeFrameChangeExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3FrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3FrameChangeExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalingExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalingExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalingExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ShearExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeShear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeShearExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ShearExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3BasisChangeExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeBasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeBasisChangeExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3BasisChangeExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeFrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeFrameChangeExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3FrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3FrameChangeExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " $" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "$" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


MUL_REALMATRIX_EXPR_REALMATRIX_EXPR::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR(coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* c, domain::DomainObject* d,interp::REALMATRIX_EXPR * operand1,interp::REALMATRIX_EXPR * operand2 ) : REALMATRIX_EXPR(c,d)
   ,operand_1(operand1),operand_2(operand2) {}

std::string MUL_REALMATRIX_EXPR_REALMATRIX_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalingExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalingExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalingExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ShearExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeShear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeShearExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ShearExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3BasisChangeExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeBasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeBasisChangeExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3BasisChangeExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeFrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeFrameChangeExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3FrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3FrameChangeExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalingExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalingExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalingExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ShearExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeShear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeShearExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ShearExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3BasisChangeExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeBasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeBasisChangeExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3BasisChangeExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeFrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeFrameChangeExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3FrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3FrameChangeExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " *" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "*" + "(" + operand_1->coords_->toString() + ")" + "(" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


REF_EXPR_REALMATRIX_VAR::REF_EXPR_REALMATRIX_VAR(coords::REF_EXPR_REALMATRIX_VAR* c, domain::DomainObject* d,interp::REALMATRIX_VAR_IDENT * operand1 ) : REALMATRIX_EXPR(c,d)
   ,operand_1(operand1) {}

std::string REF_EXPR_REALMATRIX_VAR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalingExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalingExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalingExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ShearExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeShear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeShearExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ShearExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3BasisChangeExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeBasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeBasisChangeExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3BasisChangeExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeFrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeFrameChangeExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3FrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3FrameChangeExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalingExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalingExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalingExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ShearExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeShear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeShearExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ShearExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3BasisChangeExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeBasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeBasisChangeExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3BasisChangeExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeFrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeFrameChangeExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3FrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3FrameChangeExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " %" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "%" + "(" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

REAL1_VAR_IDENT::REAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* c, domain::DomainObject* d) : Interp(c,d) {}
                    
std::string REAL1_VAR_IDENT::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
        }
    }

    if(!found){
        //ret = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "!"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                
REAL3_VAR_IDENT::REAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* c, domain::DomainObject* d) : Interp(c,d) {}
                    
std::string REAL3_VAR_IDENT::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
        }
    }

    if(!found){
        //ret = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "!"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                
REAL4_VAR_IDENT::REAL4_VAR_IDENT(coords::REAL4_VAR_IDENT* c, domain::DomainObject* d) : Interp(c,d) {}
                    
std::string REAL4_VAR_IDENT::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeHomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeHomogenousPointVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3HomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3HomogenousPointVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeHomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeHomogenousPointVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3HomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3HomogenousPointVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
        }
    }

    if(!found){
        //ret = "";
        
            auto case_coords = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "!"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                
REALMATRIX_VAR_IDENT::REALMATRIX_VAR_IDENT(coords::REALMATRIX_VAR_IDENT* c, domain::DomainObject* d) : Interp(c,d) {}
                    
std::string REALMATRIX_VAR_IDENT::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalingVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalingVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalingVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ShearVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeShear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeShearVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ShearVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3BasisChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeBasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeBasisChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3BasisChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeFrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeFrameChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3FrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3FrameChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalingVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalingVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalingVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ShearVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeShear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeShearVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ShearVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3BasisChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeBasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeBasisChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3BasisChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeFrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeFrameChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3FrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3FrameChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
        }
    }

    if(!found){
        //ret = "";
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "!"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
        }
    }

    if(!found){
        //ret = "";
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

REAL1_LITERAL1::REAL1_LITERAL1(coords::REAL1_LITERAL1* c, domain::DomainObject* d ) : REAL1_LITERAL(c,d)
    {}

std::string REAL1_LITERAL1::toString() const {
    bool found = false;
    std::string retval = "";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleExpression " +  " := "
             + " ⬝(EuclideanGeometry3AngleDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarExpression " +  " := "
             + " ⬝(ClassicalVelocity3ScalarDefault (EvalClassicalVelocity3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarExpression " +  " := "
             + " ⬝(ClassicalTimeScalarDefault (EvalClassicalTimeSpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarExpression " +  " := "
             + " ⬝(EuclideanGeometry3ScalarDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3AngleExpression " +  " := "
             + " ⬝(EuclideanGeometry3AngleDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalarExpression " +  " := "
             + " ⬝(ClassicalVelocity3ScalarDefault (EvalClassicalVelocity3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalarExpression " +  " := "
             + " ⬝(ClassicalTimeScalarDefault (EvalClassicalTimeSpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalarExpression " +  " := "
             + " ⬝(EuclideanGeometry3ScalarDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + " ⬝_ ";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
        }
    }

    if(!found){
        //ret = "";
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
	retval += "\n"+ operand_3->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "(" + operand_1->coords_->toString() + ")"+ "⬝" +"(" + operand_2->coords_->toString() + ")"+ "⬝" +"(" + operand_3->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


REAL3_LITERAL3::REAL3_LITERAL3(coords::REAL3_LITERAL3* c, domain::DomainObject* d ) : REAL3_LITERAL(c,d)
    {}

std::string REAL3_LITERAL3::toString() const {
    bool found = false;
    std::string retval = "";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " ⬝(EuclideanGeometry3RotationDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + " ⬝(EuclideanGeometry3OrientationDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + " ⬝(ClassicalVelocity3VectorDefault (EvalClassicalVelocity3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + " ⬝(ClassicalTimeVectorDefault (EvalClassicalTimeSpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + " ⬝(EuclideanGeometry3VectorDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + " ⬝(ClassicalTimePointDefault (EvalClassicalTimeSpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + " ⬝(EuclideanGeometry3PointDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " ⬝(EuclideanGeometry3RotationDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + " ⬝(EuclideanGeometry3OrientationDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3VectorExpression " +  " := "
             + " ⬝(ClassicalVelocity3VectorDefault (EvalClassicalVelocity3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeVectorExpression " +  " := "
             + " ⬝(ClassicalTimeVectorDefault (EvalClassicalTimeSpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3VectorExpression " +  " := "
             + " ⬝(EuclideanGeometry3VectorDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimePointExpression " +  " := "
             + " ⬝(ClassicalTimePointDefault (EvalClassicalTimeSpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3PointExpression " +  " := "
             + " ⬝(EuclideanGeometry3PointDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + " ⬝_ ";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

REAL4_LITERAL::REAL4_LITERAL(coords::REAL4_LITERAL* c, domain::DomainObject* d) : REAL4_EXPR(c,d) {}
                    
std::string REAL4_LITERAL::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeHomogenousPoint*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3HomogenousPoint*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeHomogenousPoint*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3HomogenousPoint*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
        }
    }

    if(!found){
        //ret = "";
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject* d,interp::REAL1_EXPR * operand1,interp::REAL1_EXPR * operand2,interp::REAL1_EXPR * operand3,interp::REAL1_EXPR * operand4 ) : REAL4_LITERAL(c,d)
   ,operand_1(operand1),operand_2(operand2),operand_3(operand3),operand_4(operand4) {}

std::string REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
	retval += "\n"+ operand_3->toString() + "\n";
	retval += "\n"+ operand_4->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeHomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeHomogenousPointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3HomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3HomogenousPointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeHomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeHomogenousPointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3HomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3HomogenousPointExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "(" + operand_1->coords_->toString() + ")"+ "⬝" +"(" + operand_2->coords_->toString() + ")"+ "⬝" +"(" + operand_3->coords_->toString() + ")"+ "⬝" +"(" + operand_4->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


REAL4_LITERAL4::REAL4_LITERAL4(coords::REAL4_LITERAL4* c, domain::DomainObject* d ) : REAL4_LITERAL(c,d)
    {}

std::string REAL4_LITERAL4::toString() const {
    bool found = false;
    std::string retval = "";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " %(EuclideanGeometry3RotationDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + " %(EuclideanGeometry3OrientationDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeHomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeHomogenousPointExpression " +  " := "
             + " %(ClassicalTimeHomogenousPointDefault (EvalClassicalTimeSpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3HomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3HomogenousPointExpression " +  " := "
             + " %(EuclideanGeometry3HomogenousPointDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " %(EuclideanGeometry3RotationDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3OrientationExpression " +  " := "
             + " %(EuclideanGeometry3OrientationDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeHomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeHomogenousPointExpression " +  " := "
             + " %(ClassicalTimeHomogenousPointDefault (EvalClassicalTimeSpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3HomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3HomogenousPointExpression " +  " := "
             + " %(EuclideanGeometry3HomogenousPointDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + " %_ ";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

REALMATRIX_LITERAL::REALMATRIX_LITERAL(coords::REALMATRIX_LITERAL* c, domain::DomainObject* d) : REALMATRIX_EXPR(c,d) {}
                    
std::string REALMATRIX_LITERAL::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scaling*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScaling*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scaling*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Shear*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeShear*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Shear*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3BasisChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeBasisChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3BasisChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeFrameChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3FrameChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scaling*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScaling*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scaling*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Shear*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeShear*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Shear*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3BasisChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeBasisChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3BasisChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeFrameChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3FrameChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
        }
    }

    if(!found){
        //ret = "";
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                

REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* c, domain::DomainObject* d,interp::REAL3_EXPR * operand1,interp::REAL3_EXPR * operand2,interp::REAL3_EXPR * operand3 ) : REALMATRIX_LITERAL(c,d)
   ,operand_1(operand1),operand_2(operand2),operand_3(operand3) {}

std::string REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
	retval += "\n"+ operand_3->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalingExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalingExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalingExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ShearExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeShear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeShearExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ShearExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3BasisChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeBasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeBasisChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3BasisChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeFrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeFrameChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3FrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3FrameChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalingExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalingExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalingExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ShearExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeShear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeShearExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ShearExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3BasisChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeBasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeBasisChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3BasisChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeFrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeFrameChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3FrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3FrameChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "(" + operand_1->coords_->toString() + ")"+ "⬝" +"(" + operand_2->coords_->toString() + ")"+ "⬝" +"(" + operand_3->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject* d,interp::REAL1_EXPR * operand1,interp::REAL1_EXPR * operand2,interp::REAL1_EXPR * operand3,interp::REAL1_EXPR * operand4,interp::REAL1_EXPR * operand5,interp::REAL1_EXPR * operand6,interp::REAL1_EXPR * operand7,interp::REAL1_EXPR * operand8,interp::REAL1_EXPR * operand9 ) : REALMATRIX_LITERAL(c,d)
   ,operand_1(operand1),operand_2(operand2),operand_3(operand3),operand_4(operand4),operand_5(operand5),operand_6(operand6),operand_7(operand7),operand_8(operand8),operand_9(operand9) {}

std::string REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::toString() const {
    bool found = false;
    std::string retval = "";
	retval += "\n"+ operand_1->toString() + "\n";
	retval += "\n"+ operand_2->toString() + "\n";
	retval += "\n"+ operand_3->toString() + "\n";
	retval += "\n"+ operand_4->toString() + "\n";
	retval += "\n"+ operand_5->toString() + "\n";
	retval += "\n"+ operand_6->toString() + "\n";
	retval += "\n"+ operand_7->toString() + "\n";
	retval += "\n"+ operand_8->toString() + "\n";
	retval += "\n"+ operand_9->toString() + "\n";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalingExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalingExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalingExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ShearExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeShear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeShearExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ShearExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3BasisChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeBasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeBasisChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3BasisChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeFrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeFrameChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3FrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3FrameChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalingExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalingExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalingExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ShearExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeShear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeShearExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ShearExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3BasisChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeBasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeBasisChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3BasisChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeFrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeFrameChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3FrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3FrameChangeExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + "(" + operand_1->coords_->toString() + ") "+ "⬝" +"(" + operand_2->coords_->toString() + ") "+ "⬝" +"(" + operand_3->coords_->toString() + ") "+ "⬝" +"(" + operand_4->coords_->toString() + ") "+ "⬝" +"(" + operand_5->coords_->toString() + ") "+ "⬝" +"(" + operand_6->coords_->toString() + ") "+ "⬝" +"(" + operand_7->coords_->toString() + ") "+ "⬝" +"(" + operand_8->coords_->toString() + ") "+ "⬝" +"(" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + "(" + operand_1->coords_->toString() + ")"+ "⬝" +"(" + operand_2->coords_->toString() + ")"+ "⬝" +"(" + operand_3->coords_->toString() + ")"+ "⬝" +"(" + operand_4->coords_->toString() + ")"+ "⬝" +"(" + operand_5->coords_->toString() + ")"+ "⬝" +"(" + operand_6->coords_->toString() + ")"+ "⬝" +"(" + operand_7->coords_->toString() + ")"+ "⬝" +"(" + operand_8->coords_->toString() + ")"+ "⬝" +"(" + operand_9->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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
                


REALMATRIX_LITERAL9::REALMATRIX_LITERAL9(coords::REALMATRIX_LITERAL9* c, domain::DomainObject* d ) : REALMATRIX_LITERAL(c,d)
    {}

std::string REALMATRIX_LITERAL9::toString() const {
    bool found = false;
    std::string retval = "";
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalingExpression " +  " := "
             + " ⬝(ClassicalVelocity3ScalingDefault (EvalClassicalVelocity3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeScaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalingExpression " +  " := "
             + " ⬝(ClassicalTimeScalingDefault (EvalClassicalTimeSpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalingExpression " +  " := "
             + " ⬝(EuclideanGeometry3ScalingDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ShearExpression " +  " := "
             + " ⬝(ClassicalVelocity3ShearDefault (EvalClassicalVelocity3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeShear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeShearExpression " +  " := "
             + " ⬝(ClassicalTimeShearDefault (EvalClassicalTimeSpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ShearExpression " +  " := "
             + " ⬝(EuclideanGeometry3ShearDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalVelocity3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3BasisChangeExpression " +  " := "
             + " ⬝(ClassicalVelocity3BasisChangeDefault (EvalClassicalVelocity3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeBasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeBasisChangeExpression " +  " := "
             + " ⬝(ClassicalTimeBasisChangeDefault (EvalClassicalTimeSpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3BasisChangeExpression " +  " := "
             + " ⬝(EuclideanGeometry3BasisChangeDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::ClassicalTimeFrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeFrameChangeExpression " +  " := "
             + " ⬝(ClassicalTimeFrameChangeDefault (EvalClassicalTimeSpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3FrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3FrameChangeExpression " +  " := "
             + " ⬝(EuclideanGeometry3FrameChangeDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " ⬝(EuclideanGeometry3RotationDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ScalingExpression " +  " := "
             + " ⬝(ClassicalVelocity3ScalingDefault (EvalClassicalVelocity3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeScaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeScalingExpression " +  " := "
             + " ⬝(ClassicalTimeScalingDefault (EvalClassicalTimeSpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ScalingExpression " +  " := "
             + " ⬝(EuclideanGeometry3ScalingDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3ShearExpression " +  " := "
             + " ⬝(ClassicalVelocity3ShearDefault (EvalClassicalVelocity3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeShear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeShearExpression " +  " := "
             + " ⬝(ClassicalTimeShearDefault (EvalClassicalTimeSpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3ShearExpression " +  " := "
             + " ⬝(EuclideanGeometry3ShearDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalVelocity3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalVelocity3BasisChangeExpression " +  " := "
             + " ⬝(ClassicalVelocity3BasisChangeDefault (EvalClassicalVelocity3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeBasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeBasisChangeExpression " +  " := "
             + " ⬝(ClassicalTimeBasisChangeDefault (EvalClassicalTimeSpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3BasisChangeExpression " +  " := "
             + " ⬝(EuclideanGeometry3BasisChangeDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::ClassicalTimeFrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ClassicalTimeFrameChangeExpression " +  " := "
             + " ⬝(ClassicalTimeFrameChangeDefault (EvalClassicalTimeSpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3FrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3FrameChangeExpression " +  " := "
             + " ⬝(EuclideanGeometry3FrameChangeDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : EuclideanGeometry3RotationExpression " +  " := "
             + " ⬝(EuclideanGeometry3RotationDefault (EvalEuclideanGeometry3SpaceExpression worldGeometrysp)) ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def " + case_coords->toString() + " : ^ := "
             + " ⬝_ ";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
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