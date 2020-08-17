#include "Interp.h"

#include "Domain.h"

#include <g3log/g3log.hpp>

#include <algorithm>
#include <unordered_map>

using namespace g3; 

namespace interp{

int GLOBAL_INDEX = 0;
std::unordered_map<Interp*,int> GLOBAL_IDS;
int ENV_INDEX = 0;

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
    
    int id = GLOBAL_IDS.count(const_cast<Space*>(this)) ? GLOBAL_IDS[const_cast<Space*>(this)] : GLOBAL_IDS[const_cast<Space*>(this)] = ++GLOBAL_INDEX + ++GLOBAL_INDEX - GLOBAL_INDEX; 
    

	if(auto dc = dynamic_cast<domain::EuclideanGeometry*>(s_)){
            found = true;
           // retval += "def " + dc->getName() + "var : lang.classicalGeometry.var := lang.classicalGeometry.var.mk " + std::to_string(id) + "" + "\n";
            //retval += "\ndef " + dc->getName() + "sp := lang.classicalGeometry.expr.lit (classicalGeometry.mk " + std::to_string(id-1) + " " + std::to_string(dc->getDimension()) + ")"; 
            retval += "\ndef " + dc->getName() + " := cmd.classicalGeometryAssmt (lang.classicalGeometry.var.mk " + std::to_string(id) + ") (lang.classicalGeometry.expr.lit(classicalGeometry.mk " + std::to_string(id) + " " + std::to_string(dc->getDimension()) + ")"")\n";
            retval += "\n def " + getEnvName() + " := cmdEval " + dc->getName() + " " + getLastEnv();
    }
	if(auto dc = dynamic_cast<domain::ClassicalTime*>(s_)){
            found = true;
           // retval += "def " + dc->getName() + "var : lang.classicalTime.var := lang.classicalTime.var.mk " + std::to_string(id) + "" + "\n";
            //retval += "\ndef " + dc->getName() + "sp := lang.classicalTime.expr.lit (classicalTime.mk " + std::to_string(id) + ")"; 
            retval += "\ndef " + dc->getName() + " := cmd.classicalTimeAssmt (lang.classicalTime.var.mk " + std::to_string(id) + ") (lang.classicalTime.expr.lit(classicalTime.mk " + std::to_string(id-1) + ")"")\n";
            retval += "\n def " + getEnvName() + " := cmdEval " + dc->getName() + " " + getLastEnv();
    }

    if(!found){
        //retval = "--Unknown space type - Translation Failed!";
    }

    return retval;
};

std::string Space::getVarExpr() const {
    
	if(auto dc = dynamic_cast<domain::EuclideanGeometry*>(s_)){
            int id = GLOBAL_IDS.count(const_cast<Space*>(this)) ? GLOBAL_IDS[const_cast<Space*>(this)] : GLOBAL_IDS[const_cast<Space*>(this)] = ++GLOBAL_INDEX + ++GLOBAL_INDEX - GLOBAL_INDEX; 
    
            return "lang.classicalGeometry.expr.var (lang.classicalGeometry.var.mk " + std::to_string(id) + ")";

    }
	if(auto dc = dynamic_cast<domain::ClassicalTime*>(s_)){
            int id = GLOBAL_IDS.count(const_cast<Space*>(this)) ? GLOBAL_IDS[const_cast<Space*>(this)] : GLOBAL_IDS[const_cast<Space*>(this)] = ++GLOBAL_INDEX + ++GLOBAL_INDEX - GLOBAL_INDEX; 
    
            return "lang.classicalTime.expr.var (lang.classicalTime.var.mk " + std::to_string(id) + ")";

    }
	if(auto dc = dynamic_cast<domain::ClassicalVelocity*>(s_)){
            int id = GLOBAL_IDS.count(const_cast<Space*>(this)) ? GLOBAL_IDS[const_cast<Space*>(this)] : GLOBAL_IDS[const_cast<Space*>(this)] = ++GLOBAL_INDEX + ++GLOBAL_INDEX - GLOBAL_INDEX; 
    
            return "lang.classicalVelocity.expr.var (lang.classicalVelocity.var.mk " + std::to_string(id) + ")";

    }
}

std::string Space::getEvalExpr() const {
    auto lastEnv = getLastEnv();


	if(auto dc = dynamic_cast<domain::EuclideanGeometry*>(s_)){
            int id = GLOBAL_IDS.count(const_cast<Space*>(this)) ? GLOBAL_IDS[const_cast<Space*>(this)] : GLOBAL_IDS[const_cast<Space*>(this)] = ++GLOBAL_INDEX + ++GLOBAL_INDEX - GLOBAL_INDEX; 
    
            return "(lang.classicalGeometry.eval (lang.classicalGeometry.expr.var (lang.classicalGeometry.var.mk " + std::to_string(id) + ")) (classicalGeometryGet " + lastEnv + ") )";

    }
	if(auto dc = dynamic_cast<domain::ClassicalTime*>(s_)){
            int id = GLOBAL_IDS.count(const_cast<Space*>(this)) ? GLOBAL_IDS[const_cast<Space*>(this)] : GLOBAL_IDS[const_cast<Space*>(this)] = ++GLOBAL_INDEX + ++GLOBAL_INDEX - GLOBAL_INDEX; 
    
            return "(lang.classicalTime.eval (lang.classicalTime.expr.var (lang.classicalTime.var.mk " + std::to_string(id) + ")) (classicalTimeGet " + lastEnv + ") )";

    }
	if(auto dc = dynamic_cast<domain::ClassicalVelocity*>(s_)){
            int id = GLOBAL_IDS.count(const_cast<Space*>(this)) ? GLOBAL_IDS[const_cast<Space*>(this)] : GLOBAL_IDS[const_cast<Space*>(this)] = ++GLOBAL_INDEX + ++GLOBAL_INDEX - GLOBAL_INDEX; 
    
            return "(lang.classicalVelocity.eval (lang.classicalVelocity.expr.var (lang.classicalVelocity.var.mk " + std::to_string(id) + ")) (classicalVelocityGet " + lastEnv + ") )";

    }

}

std::string DerivedSpace::toString() const {
    std::string retval = "";
    bool found = false;
    
    int id = GLOBAL_IDS.count(const_cast<DerivedSpace*>(this)) ? GLOBAL_IDS[const_cast<DerivedSpace*>(this)] : GLOBAL_IDS[const_cast<DerivedSpace*>(this)] = ++GLOBAL_INDEX + ++GLOBAL_INDEX - GLOBAL_INDEX; 
    

	if(auto dc = dynamic_cast<domain::ClassicalVelocity*>(s_)){
            found = true;
            auto currentEnv = getEnvName();
            //retval += "def " + dc->getName() + "var : lang.classicalVelocity.var := lang.classicalVelocity.var.mk " + std::to_string(id) + "" + "\n";
            //retval += "\ndef " + dc->getName() + "sp := lang.classicalVelocity.expr.lit (classicalVelocity.mk " + std::to_string(id) + " " + dc->getBase1()->getName() + " " + dc->getBase2()->getName() +  ")"; 
            retval += "\ndef " + dc->getName() + " := cmd.classicalVelocityAssmt \n\t\t(lang.classicalVelocity.var.mk " + std::to_string(id) + ") \n\t\t(lang.classicalVelocity.expr.lit (classicalVelocity.mk " + std::to_string(id-1) + " \n\t\t\t" + this->base_1->getEvalExpr() + " \n\t\t\t" + this->base_2->getEvalExpr() +  "))\n";
            retval += "\n def " + currentEnv + " := cmdEval " + dc->getName() + " " + getLastEnv();
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
        retval += "def " +dc->getName()+"."+f_->getName() + "var : classicalGeometryFrameVar := (!" + std::to_string(++GLOBAL_INDEX) + ")" + "\n";
        if(!isStandard){
            retval += "def " + dc->getName()+"."+f_->getName() + "fr := classicalGeometryFrameExpression.FrameLiteral ( BuildEuclideanGeometryFrame "+ dc->getName()+"))";
        }
        else{
            retval += "def " + dc->getName()+"."+f_->getName() + "fr := classicalGeometryFrameExpression.FrameLiteral ( GetEuclideanGeometryStandardFrame (EvalclassicalGeometrySpaceExpression " + dc->getName()+"sp))\n";
    
        }
        retval += "def " + dc->getName()+"."+f_->getName() + " := PhysGlobalCommand.GlobalFrame (⊢" + dc->getName()+"."+f_->getName() + "var) (⊢" + dc->getName()+"."+f_->getName() + "fr)\n";
    }
	if(auto dc = dynamic_cast<domain::ClassicalTime*>(f_->getSpace())){
        found = true;
        retval += "def " +dc->getName()+"."+f_->getName() + "var : classicalTimeFrameVar := (!" + std::to_string(++GLOBAL_INDEX) + ")" + "\n";
        if(!isStandard){
            retval += "def " + dc->getName()+"."+f_->getName() + "fr := classicalTimeFrameExpression.FrameLiteral ( BuildClassicalTimeFrame "+ dc->getName()+"))";
        }
        else{
            retval += "def " + dc->getName()+"."+f_->getName() + "fr := classicalTimeFrameExpression.FrameLiteral ( GetClassicalTimeStandardFrame (EvalclassicalTimeSpaceExpression " + dc->getName()+"sp))\n";
    
        }
        retval += "def " + dc->getName()+"."+f_->getName() + " := PhysGlobalCommand.GlobalFrame (⊢" + dc->getName()+"."+f_->getName() + "var) (⊢" + dc->getName()+"."+f_->getName() + "fr)\n";
    }
	if(auto dc = dynamic_cast<domain::ClassicalVelocity*>(f_->getSpace())){
        found = true;
        retval += "def " +dc->getName()+"."+f_->getName() + "var : classicalVelocityFrameVar := (!" + std::to_string(++GLOBAL_INDEX) + ")" + "\n";
        if(!isStandard){
            retval += "def " + dc->getName()+"."+f_->getName() + "fr := classicalVelocityFrameExpression.FrameLiteral ( BuildClassicalVelocityFrame "+ dc->getName()+"))";
        }
        else{
            retval += "def " + dc->getName()+"."+f_->getName() + "fr := classicalVelocityFrameExpression.FrameLiteral ( GetClassicalVelocityStandardFrame (EvalclassicalVelocitySpaceExpression " + dc->getName()+"sp))\n";
    
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
    //ret += "def var_" + std::to_string(++GLOBAL_INDEX) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //ret = "";
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
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
std::string SEQ_GLOBALSTMT::toStringLinked(std::vector<interp::Space*> links, std::vector<std::string> names, std::vector<interp::Frame*> framelinks, std::vector<string> framenames, bool before) { 
    //std::string toStr = this->toString();
    std::string retval = "";
    string cmdvalstart = "::[]";
    string cmdval = "";
    int i = 0;

    std::string cmdwrapper = "PhysCommand.Seq";

    int count = this->operands_.size() + links.size() + framelinks.size();
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
        /*for(auto op: framelinks){
            if(prev){
                retval += "\n" + op->toString() + "\n";
                cmdval = "(" + cmdwrapper + " " + framenames[i++] + " " + cmdval + ")";
            }
            else{
                retval += "\n" + op->toString() + "\n";
                cmdval = framenames[i++];
                prev = true;
            }
        }*/

        bool start = true;
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
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++GLOBAL_INDEX) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //ret = "";
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
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
                
STMT::STMT(coords::STMT* c, domain::DomainObject* d) : Interp(c,d) {}
                    
std::string STMT::toString() const {
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
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
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
std::string COMPOUND_STMT::toStringLinked(std::vector<interp::Space*> links, std::vector<std::string> names, std::vector<interp::Frame*> framelinks, std::vector<string> framenames, bool before) { 
    //std::string toStr = this->toString();
    std::string retval = "";
    string cmdvalstart = "::[]";
    string cmdval = "";
    int i = 0;

    std::string cmdwrapper = "cmd.seq";

    int count = this->operands_.size() + links.size() + framelinks.size();
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
        /*for(auto op: framelinks){
            if(prev){
                retval += "\n" + op->toString() + "\n";
                cmdval = "(" + cmdwrapper + " " + framenames[i++] + " " + cmdval + ")";
            }
            else{
                retval += "\n" + op->toString() + "\n";
                cmdval = framenames[i++];
                prev = true;
            }
        }*/

        bool start = true;
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
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++GLOBAL_INDEX) + ":= 1";
    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
        }
    }

    if(!found){
        //ret = "";
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
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
                

VOID_FUNC_DECL_STMT::VOID_FUNC_DECL_STMT(coords::VOID_FUNC_DECL_STMT* c, domain::DomainObject* d,interp::STMT * operand1 ) : FUNC_DECL(c,d)
   ,operand_1(operand1) {}

std::string VOID_FUNC_DECL_STMT::toString() const {
    std::string ret = "";
    //  ret += "(";
    ret += "def var_" + std::to_string(++GLOBAL_INDEX) + ":= 1";
     return ret;
}




MAIN_FUNC_DECL_STMT::MAIN_FUNC_DECL_STMT(coords::MAIN_FUNC_DECL_STMT* c, domain::DomainObject* d,interp::STMT * operand1 ) : FUNC_DECL(c,d)
   ,operand_1(operand1) {}

std::string MAIN_FUNC_DECL_STMT::toString() const {
    std::string ret = "";
    //  ret += "(";
    ret += "def var_" + std::to_string(++GLOBAL_INDEX) + ":= 1";
     return ret;
}


} // namespace coords