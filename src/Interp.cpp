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
        retval += "def " + dc->getName() + " := EuclideanGeometry " + " \"" + dc->getName() + "\" " + std::to_string(dc->getDimension()); 

    }
	if(auto dc = dynamic_cast<domain::ClassicalTime*>(s_)){
        found = true;
        retval += "def " + dc->getName() + " := ClassicalTime " + " \"" + dc->getName() + "\"  ";

    }
	if(auto dc = dynamic_cast<domain::ClassicalVelocity*>(s_)){
        found = true;
        retval += "def " + dc->getName() + " := ClassicalVelocity " + " \"" + dc->getName() + "\" " + std::to_string(dc->getDimension()); 

    }

    if(!found){
        //retval = "--Unknown space type - Translation Failed!";
    }

    return retval;
};

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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
    }
    
    
    return retval;
}
                
COMPOUND_STMT::COMPOUND_STMT(coords::COMPOUND_STMT* c, domain::DomainObject* d, std::vector<STMT*> operands)  :STMT(c, d) {
    for(auto& op : operands){
        this->operands_.push_back(op);
    }

};
std::string COMPOUND_STMT::toString() const{ 
    std::string retval = "";
    for(auto op: this->operands_){ 
        retval += "\n" + op->toString() + "\n";
    }
    //std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
            retval += "def STMT" + case_coords->toString() + " : ^ := "
             + "(REAL1.VAR.IDENT" + operand_1->coords_->toString() + ")"+ "=" +"(REAL1.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
            retval += "def STMT" + case_coords->toString() + " : ^ := "
             + "(REAL3.VAR.IDENT" + operand_1->coords_->toString() + ")"+ "=" +"(REAL3.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
            retval += "def STMT" + case_coords->toString() + " : ^ := "
             + "(REAL4.VAR.IDENT" + operand_1->coords_->toString() + ")"+ "=" +"(REAL4.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
            retval += "def STMT" + case_coords->toString() + " : ^ := "
             + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")"+ "=" +"(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
            retval += "def STMT" + case_coords->toString() + " : ^ := "
             + "(REAL1.VAR.IDENT" + operand_1->coords_->toString() + ")"+ "=" +"(REAL1.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
            retval += "def STMT" + case_coords->toString() + " : ^ := "
             + "(REAL3.VAR.IDENT" + operand_1->coords_->toString() + ")"+ "=" +"(REAL3.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
            retval += "def STMT" + case_coords->toString() + " : ^ := "
             + "(REAL4.VAR.IDENT" + operand_1->coords_->toString() + ")"+ "=" +"(REAL4.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
            retval += "def STMT" + case_coords->toString() + " : ^ := "
             + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")"+ "=" +"(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
    }
    

    return retval;
}
                

REAL1_EXPR::REAL1_EXPR(coords::REAL1_EXPR* c, domain::DomainObject* d) : EXPR(c,d) {}
                    
std::string REAL1_EXPR::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::Geometric3Angle*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::TimeScalar*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Angle*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::TimeScalar*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(cont->getValue())){
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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3AngleExpression " +  " := "
             + " $" + "(REAL1.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Velocity3ScalarExpression " +  " := "
             + " $" + "(REAL1.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : TimeScalarExpression " +  " := "
             + " $" + "(REAL1.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3ScalarExpression " +  " := "
             + " $" + "(REAL1.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3AngleExpression " +  " := "
             + " $" + "(REAL1.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Velocity3ScalarExpression " +  " := "
             + " $" + "(REAL1.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : TimeScalarExpression " +  " := "
             + " $" + "(REAL1.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3ScalarExpression " +  " := "
             + " $" + "(REAL1.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1.EXPR" + case_coords->toString() + " : ^ := "
             + "$" + "(REAL1.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3AngleExpression " +  " := "
             + "(REAL1_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Velocity3ScalarExpression " +  " := "
             + "(REAL1_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : TimeScalarExpression " +  " := "
             + "(REAL1_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3ScalarExpression " +  " := "
             + "(REAL1_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3AngleExpression " +  " := "
             + "(REAL1_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Velocity3ScalarExpression " +  " := "
             + "(REAL1_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : TimeScalarExpression " +  " := "
             + "(REAL1_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3ScalarExpression " +  " := "
             + "(REAL1_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1.EXPR" + case_coords->toString() + " : ^ := "
             + " (REAL1_EXPR" + operand_1->coords_->toString() + ") + " + "⁻¹";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3AngleExpression " +  " := "
             + " -" + "(REAL1.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Velocity3ScalarExpression " +  " := "
             + " -" + "(REAL1.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : TimeScalarExpression " +  " := "
             + " -" + "(REAL1.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3ScalarExpression " +  " := "
             + " -" + "(REAL1.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3AngleExpression " +  " := "
             + " -" + "(REAL1.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Velocity3ScalarExpression " +  " := "
             + " -" + "(REAL1.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : TimeScalarExpression " +  " := "
             + " -" + "(REAL1.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3ScalarExpression " +  " := "
             + " -" + "(REAL1.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1.EXPR" + case_coords->toString() + " : ^ := "
             + "-" + "(REAL1.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3AngleExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "+" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Velocity3ScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "+" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : TimeScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "+" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3ScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "+" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3AngleExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "+" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Velocity3ScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "+" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : TimeScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "+" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3ScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "+" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1.EXPR" + case_coords->toString() + " : ^ := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ")"+ "+" +"(REAL1.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3AngleExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Velocity3ScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : TimeScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3ScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3AngleExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Velocity3ScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : TimeScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3ScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1.EXPR" + case_coords->toString() + " : ^ := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ")"+ "-" +"(REAL1.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3AngleExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Velocity3ScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : TimeScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3ScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3AngleExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Velocity3ScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : TimeScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3ScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1.EXPR" + case_coords->toString() + " : ^ := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ")"+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3AngleExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Velocity3ScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : TimeScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3ScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3AngleExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Velocity3ScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : TimeScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3ScalarExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1.EXPR" + case_coords->toString() + " : ^ := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ")"+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3AngleExpression " +  " := "
             + " %" + "(REAL1.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Velocity3ScalarExpression " +  " := "
             + " %" + "(REAL1.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : TimeScalarExpression " +  " := "
             + " %" + "(REAL1.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3ScalarExpression " +  " := "
             + " %" + "(REAL1.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3AngleExpression " +  " := "
             + " %" + "(REAL1.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Velocity3ScalarExpression " +  " := "
             + " %" + "(REAL1.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : TimeScalarExpression " +  " := "
             + " %" + "(REAL1.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3ScalarExpression " +  " := "
             + " %" + "(REAL1.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1.EXPR" + case_coords->toString() + " : ^ := "
             + "%" + "(REAL1.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
    }
    

    return retval;
}
                

REAL3_EXPR::REAL3_EXPR(coords::REAL3_EXPR* c, domain::DomainObject* d) : EXPR(c,d) {}
                    
std::string REAL3_EXPR::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Velocity3Vector*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::TimeVector*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3Vector*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::TimePoint*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3Point*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Velocity3Vector*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::TimeVector*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3Vector*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::TimePoint*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3Point*>(cont->getValue())){
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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " $" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + " $" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + " $" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + " $" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + " $" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + " $" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + " $" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " $" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + " $" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + " $" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + " $" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + " $" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + " $" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + " $" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3.EXPR" + case_coords->toString() + " : ^ := "
             + "$" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " +" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")" + "(REAL3.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + " +" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")" + "(REAL3.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + " +" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")" + "(REAL3.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + " +" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")" + "(REAL3.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + " +" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")" + "(REAL3.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + " +" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")" + "(REAL3.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + " +" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")" + "(REAL3.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " +" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")" + "(REAL3.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + " +" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")" + "(REAL3.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + " +" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")" + "(REAL3.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + " +" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")" + "(REAL3.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + " +" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")" + "(REAL3.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + " +" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")" + "(REAL3.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + " +" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")" + "(REAL3.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3.EXPR" + case_coords->toString() + " : ^ := "
             + "+" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")" + "(REAL3.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "-" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3.EXPR" + case_coords->toString() + " : ^ := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ")"+ "-" +"(REAL3.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL3_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + "(REAL3_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + "(REAL3_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + "(REAL3_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + "(REAL3_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + "(REAL3_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + "(REAL3_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL3_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + "(REAL3_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + "(REAL3_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + "(REAL3_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + "(REAL3_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + "(REAL3_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + "(REAL3_EXPR" + operand_1->coords_->toString() + ") " + " ⁻¹ ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3.EXPR" + case_coords->toString() + " : ^ := "
             + " (REAL3_EXPR" + operand_1->coords_->toString() + ") + " + "⁻¹";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " -" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + " -" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + " -" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + " -" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + " -" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + " -" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + " -" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " -" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + " -" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + " -" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + " -" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + " -" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + " -" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + " -" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3.EXPR" + case_coords->toString() + " : ^ := "
             + "-" + "(REAL3.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3.EXPR" + case_coords->toString() + " : ^ := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ")"+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3.EXPR" + case_coords->toString() + " : ^ := "
             + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")"+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3.EXPR" + case_coords->toString() + " : ^ := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ")"+ "/" +"(REAL1.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " %" + "(REAL3.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + " %" + "(REAL3.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + " %" + "(REAL3.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + " %" + "(REAL3.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + " %" + "(REAL3.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + " %" + "(REAL3.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + " %" + "(REAL3.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " %" + "(REAL3.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + " %" + "(REAL3.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + " %" + "(REAL3.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + " %" + "(REAL3.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + " %" + "(REAL3.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + " %" + "(REAL3.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + " %" + "(REAL3.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3.EXPR" + case_coords->toString() + " : ^ := "
             + "%" + "(REAL3.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
    }
    

    return retval;
}
                

REAL4_EXPR::REAL4_EXPR(coords::REAL4_EXPR* c, domain::DomainObject* d) : EXPR(c,d) {}
                    
std::string REAL4_EXPR::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::TimeHomogenousPoint*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3HomogenousPoint*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::TimeHomogenousPoint*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3HomogenousPoint*>(cont->getValue())){
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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " $" + "(REAL4.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + " $" + "(REAL4.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeHomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : TimeHomogenousPointExpression " +  " := "
             + " $" + "(REAL4.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3HomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3HomogenousPointExpression " +  " := "
             + " $" + "(REAL4.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " $" + "(REAL4.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + " $" + "(REAL4.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeHomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : TimeHomogenousPointExpression " +  " := "
             + " $" + "(REAL4.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3HomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3HomogenousPointExpression " +  " := "
             + " $" + "(REAL4.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4.EXPR" + case_coords->toString() + " : ^ := "
             + "$" + "(REAL4.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL4.EXPR" + operand_1->coords_->toString() + ") "+ "+" +"(REAL4.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + "(REAL4.EXPR" + operand_1->coords_->toString() + ") "+ "+" +"(REAL4.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeHomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : TimeHomogenousPointExpression " +  " := "
             + "(REAL4.EXPR" + operand_1->coords_->toString() + ") "+ "+" +"(REAL4.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3HomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3HomogenousPointExpression " +  " := "
             + "(REAL4.EXPR" + operand_1->coords_->toString() + ") "+ "+" +"(REAL4.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL4.EXPR" + operand_1->coords_->toString() + ") "+ "+" +"(REAL4.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + "(REAL4.EXPR" + operand_1->coords_->toString() + ") "+ "+" +"(REAL4.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeHomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : TimeHomogenousPointExpression " +  " := "
             + "(REAL4.EXPR" + operand_1->coords_->toString() + ") "+ "+" +"(REAL4.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3HomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3HomogenousPointExpression " +  " := "
             + "(REAL4.EXPR" + operand_1->coords_->toString() + ") "+ "+" +"(REAL4.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4.EXPR" + case_coords->toString() + " : ^ := "
             + "(REAL4.EXPR" + operand_1->coords_->toString() + ")"+ "+" +"(REAL4.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL4.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + "(REAL4.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeHomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : TimeHomogenousPointExpression " +  " := "
             + "(REAL4.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3HomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3HomogenousPointExpression " +  " := "
             + "(REAL4.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL4.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + "(REAL4.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeHomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : TimeHomogenousPointExpression " +  " := "
             + "(REAL4.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3HomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3HomogenousPointExpression " +  " := "
             + "(REAL4.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4.EXPR" + case_coords->toString() + " : ^ := "
             + "(REAL4.EXPR" + operand_1->coords_->toString() + ")"+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " %" + "(REAL4.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + " %" + "(REAL4.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeHomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : TimeHomogenousPointExpression " +  " := "
             + " %" + "(REAL4.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3HomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3HomogenousPointExpression " +  " := "
             + " %" + "(REAL4.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " %" + "(REAL4.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + " %" + "(REAL4.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeHomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : TimeHomogenousPointExpression " +  " := "
             + " %" + "(REAL4.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3HomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3HomogenousPointExpression " +  " := "
             + " %" + "(REAL4.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4.EXPR" + case_coords->toString() + " : ^ := "
             + "%" + "(REAL4.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
    }
    

    return retval;
}
                

REALMATRIX_EXPR::REALMATRIX_EXPR(coords::REALMATRIX_EXPR* c, domain::DomainObject* d) : EXPR(c,d) {}
                    
std::string REALMATRIX_EXPR::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::Velocity3Scaling*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::TimeScaling*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scaling*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Velocity3Shear*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::TimeShear*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3Shear*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Velocity3BasisChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::TimeBasisChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3BasisChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::TimeFrameChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3FrameChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Velocity3Scaling*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::TimeScaling*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scaling*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Velocity3Shear*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::TimeShear*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3Shear*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Velocity3BasisChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::TimeBasisChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3BasisChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::TimeFrameChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3FrameChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Velocity3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ScalingExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeScaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeScalingExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ScalingExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ShearExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeShear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeShearExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ShearExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3BasisChangeExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeBasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeBasisChangeExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3BasisChangeExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeFrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeFrameChangeExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3FrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3FrameChangeExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Velocity3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ScalingExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeScaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeScalingExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ScalingExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ShearExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeShear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeShearExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ShearExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3BasisChangeExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeBasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeBasisChangeExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3BasisChangeExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeFrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeFrameChangeExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3FrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3FrameChangeExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " $" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX.EXPR" + case_coords->toString() + " : ^ := "
             + "$" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Velocity3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ScalingExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeScaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeScalingExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ScalingExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ShearExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeShear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeShearExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ShearExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3BasisChangeExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeBasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeBasisChangeExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3BasisChangeExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeFrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeFrameChangeExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3FrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3FrameChangeExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Velocity3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ScalingExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeScaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeScalingExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ScalingExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ShearExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeShear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeShearExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ShearExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3BasisChangeExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeBasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeBasisChangeExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3BasisChangeExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeFrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeFrameChangeExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3FrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3FrameChangeExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " *" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX.EXPR" + case_coords->toString() + " : ^ := "
             + "*" + "(REALMATRIX.EXPR" + operand_1->coords_->toString() + ")" + "(REALMATRIX.EXPR" + operand_2->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Velocity3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ScalingExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeScaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeScalingExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ScalingExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ShearExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeShear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeShearExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ShearExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3BasisChangeExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeBasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeBasisChangeExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3BasisChangeExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeFrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeFrameChangeExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3FrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3FrameChangeExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Velocity3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ScalingExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeScaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeScalingExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ScalingExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ShearExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeShear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeShearExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ShearExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3BasisChangeExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeBasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeBasisChangeExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3BasisChangeExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeFrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeFrameChangeExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3FrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3FrameChangeExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " %" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX.EXPR" + case_coords->toString() + " : ^ := "
             + "%" + "(REALMATRIX.VAR.IDENT" + operand_1->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
    }
    

    return retval;
}
                

REAL1_VAR_IDENT::REAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* c, domain::DomainObject* d) : Interp(c,d) {}
                    
std::string REAL1_VAR_IDENT::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::Geometric3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->coords_);
            retval += "def REAL1_VAR_IDENT" + case_coords->toString() + " : Geometric3AngleVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->coords_);
            retval += "def REAL1_VAR_IDENT" + case_coords->toString() + " : Velocity3ScalarVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->coords_);
            retval += "def REAL1_VAR_IDENT" + case_coords->toString() + " : TimeScalarVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->coords_);
            retval += "def REAL1_VAR_IDENT" + case_coords->toString() + " : Geometric3ScalarVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->coords_);
            retval += "def REAL1_VAR_IDENT" + case_coords->toString() + " : Geometric3AngleVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->coords_);
            retval += "def REAL1_VAR_IDENT" + case_coords->toString() + " : Velocity3ScalarVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->coords_);
            retval += "def REAL1_VAR_IDENT" + case_coords->toString() + " : TimeScalarVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->coords_);
            retval += "def REAL1_VAR_IDENT" + case_coords->toString() + " : Geometric3ScalarVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
        }
    }

    if(!found){
        //ret = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->coords_);
            retval += "def REAL1.VAR.IDENT" + case_coords->toString() + " : ^ := "
             + "!"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
    }
    
    
    return retval;
}
                
REAL3_VAR_IDENT::REAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* c, domain::DomainObject* d) : Interp(c,d) {}
                    
std::string REAL3_VAR_IDENT::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def REAL3_VAR_IDENT" + case_coords->toString() + " : Geometric3RotationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def REAL3_VAR_IDENT" + case_coords->toString() + " : Geometric3OrientationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def REAL3_VAR_IDENT" + case_coords->toString() + " : Velocity3VectorVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def REAL3_VAR_IDENT" + case_coords->toString() + " : TimeVectorVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def REAL3_VAR_IDENT" + case_coords->toString() + " : Geometric3VectorVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def REAL3_VAR_IDENT" + case_coords->toString() + " : TimePointVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def REAL3_VAR_IDENT" + case_coords->toString() + " : Geometric3PointVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def REAL3_VAR_IDENT" + case_coords->toString() + " : Geometric3RotationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def REAL3_VAR_IDENT" + case_coords->toString() + " : Geometric3OrientationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def REAL3_VAR_IDENT" + case_coords->toString() + " : Velocity3VectorVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def REAL3_VAR_IDENT" + case_coords->toString() + " : TimeVectorVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def REAL3_VAR_IDENT" + case_coords->toString() + " : Geometric3VectorVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def REAL3_VAR_IDENT" + case_coords->toString() + " : TimePointVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def REAL3_VAR_IDENT" + case_coords->toString() + " : Geometric3PointVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
        }
    }

    if(!found){
        //ret = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->coords_);
            retval += "def REAL3.VAR.IDENT" + case_coords->toString() + " : ^ := "
             + "!"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
    }
    
    
    return retval;
}
                
REAL4_VAR_IDENT::REAL4_VAR_IDENT(coords::REAL4_VAR_IDENT* c, domain::DomainObject* d) : Interp(c,d) {}
                    
std::string REAL4_VAR_IDENT::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->coords_);
            retval += "def REAL4_VAR_IDENT" + case_coords->toString() + " : Geometric3RotationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->coords_);
            retval += "def REAL4_VAR_IDENT" + case_coords->toString() + " : Geometric3OrientationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeHomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->coords_);
            retval += "def REAL4_VAR_IDENT" + case_coords->toString() + " : TimeHomogenousPointVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3HomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->coords_);
            retval += "def REAL4_VAR_IDENT" + case_coords->toString() + " : Geometric3HomogenousPointVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->coords_);
            retval += "def REAL4_VAR_IDENT" + case_coords->toString() + " : Geometric3RotationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->coords_);
            retval += "def REAL4_VAR_IDENT" + case_coords->toString() + " : Geometric3OrientationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeHomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->coords_);
            retval += "def REAL4_VAR_IDENT" + case_coords->toString() + " : TimeHomogenousPointVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3HomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->coords_);
            retval += "def REAL4_VAR_IDENT" + case_coords->toString() + " : Geometric3HomogenousPointVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
        }
    }

    if(!found){
        //ret = "";
        
            auto case_coords = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->coords_);
            retval += "def REAL4.VAR.IDENT" + case_coords->toString() + " : ^ := "
             + "!"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
    }
    
    
    return retval;
}
                
REALMATRIX_VAR_IDENT::REALMATRIX_VAR_IDENT(coords::REALMATRIX_VAR_IDENT* c, domain::DomainObject* d) : Interp(c,d) {}
                    
std::string REALMATRIX_VAR_IDENT::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::Velocity3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : Velocity3ScalingVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeScaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : TimeScalingVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : Geometric3ScalingVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : Velocity3ShearVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeShear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : TimeShearVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : Geometric3ShearVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : Velocity3BasisChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeBasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : TimeBasisChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : Geometric3BasisChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeFrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : TimeFrameChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3FrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : Geometric3FrameChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : Geometric3RotationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Velocity3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : Velocity3ScalingVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeScaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : TimeScalingVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : Geometric3ScalingVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : Velocity3ShearVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeShear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : TimeShearVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : Geometric3ShearVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : Velocity3BasisChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeBasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : TimeBasisChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : Geometric3BasisChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeFrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : TimeFrameChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3FrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : Geometric3FrameChangeVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX_VAR_IDENT" + case_coords->toString() + " : Geometric3RotationVar " +  " := "
             + " !"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
            }
        }
    }

    if(!found){
        //ret = "";
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->coords_);
            retval += "def REALMATRIX.VAR.IDENT" + case_coords->toString() + " : ^ := "
             + "!"+ std::to_string(++GLOBAL_INDEX);
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
    }
    
    
    return retval;
}
                
REAL1_LITERAL::REAL1_LITERAL(coords::REAL1_LITERAL* c, domain::DomainObject* d) : REAL1_EXPR(c,d) {}
                    
std::string REAL1_LITERAL::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::Geometric3Angle*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::TimeScalar*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Angle*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::TimeScalar*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(cont->getValue())){
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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Angle*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3AngleExpression " +  " := "
             + " ⬝(Geometric3AngleDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Velocity3ScalarExpression " +  " := "
             + " ⬝(Velocity3ScalarDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeScalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : TimeScalarExpression " +  " := "
             + " ⬝(TimeScalarDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3ScalarExpression " +  " := "
             + " ⬝(Geometric3ScalarDefault worldGeometry) ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Angle*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3AngleExpression " +  " := "
             + " ⬝(Geometric3AngleDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Velocity3ScalarExpression " +  " := "
             + " ⬝(Velocity3ScalarDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeScalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : TimeScalarExpression " +  " := "
             + " ⬝(TimeScalarDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scalar*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1_EXPR" + case_coords->toString() + " : Geometric3ScalarExpression " +  " := "
             + " ⬝(Geometric3ScalarDefault worldGeometry) ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL1_EXPR*>(this->coords_);
            retval += "def REAL1.EXPR" + case_coords->toString() + " : ^ := "
             + " ⬝_ ";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
    }
    

    return retval;
}
                

REAL3_LITERAL::REAL3_LITERAL(coords::REAL3_LITERAL* c, domain::DomainObject* d) : REAL3_EXPR(c,d) {}
                    
std::string REAL3_LITERAL::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Velocity3Vector*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::TimeVector*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3Vector*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::TimePoint*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3Point*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Velocity3Vector*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::TimeVector*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3Vector*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::TimePoint*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3Point*>(cont->getValue())){
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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3.EXPR" + case_coords->toString() + " : ^ := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ")"+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ")"+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " ⬝(Geometric3RotationDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + " ⬝(Geometric3OrientationDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + " ⬝(Velocity3VectorDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeVector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + " ⬝(TimeVectorDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Vector*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + " ⬝(Geometric3VectorDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimePoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + " ⬝(TimePointDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Point*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + " ⬝(Geometric3PointDefault worldGeometry) ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " ⬝(Geometric3RotationDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + " ⬝(Geometric3OrientationDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Velocity3VectorExpression " +  " := "
             + " ⬝(Velocity3VectorDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeVector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimeVectorExpression " +  " := "
             + " ⬝(TimeVectorDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Vector*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3VectorExpression " +  " := "
             + " ⬝(Geometric3VectorDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimePoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : TimePointExpression " +  " := "
             + " ⬝(TimePointDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Point*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3_EXPR" + case_coords->toString() + " : Geometric3PointExpression " +  " := "
             + " ⬝(Geometric3PointDefault worldGeometry) ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL3_EXPR*>(this->coords_);
            retval += "def REAL3.EXPR" + case_coords->toString() + " : ^ := "
             + " ⬝_ ";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
    }
    

    return retval;
}
                

REAL4_LITERAL::REAL4_LITERAL(coords::REAL4_LITERAL* c, domain::DomainObject* d) : REAL4_EXPR(c,d) {}
                    
std::string REAL4_LITERAL::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::TimeHomogenousPoint*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3HomogenousPoint*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::TimeHomogenousPoint*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3HomogenousPoint*>(cont->getValue())){
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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeHomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : TimeHomogenousPointExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3HomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3HomogenousPointExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeHomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : TimeHomogenousPointExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3HomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3HomogenousPointExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4.EXPR" + case_coords->toString() + " : ^ := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ")"+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ")"+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ")"+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " %(Geometric3RotationDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + " %(Geometric3OrientationDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeHomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : TimeHomogenousPointExpression " +  " := "
             + " %(TimeHomogenousPointDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3HomogenousPoint*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3HomogenousPointExpression " +  " := "
             + " %(Geometric3HomogenousPointDefault worldGeometry) ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " %(Geometric3RotationDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Orientation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3OrientationExpression " +  " := "
             + " %(Geometric3OrientationDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeHomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : TimeHomogenousPointExpression " +  " := "
             + " %(TimeHomogenousPointDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3HomogenousPoint*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4_EXPR" + case_coords->toString() + " : Geometric3HomogenousPointExpression " +  " := "
             + " %(Geometric3HomogenousPointDefault worldGeometry) ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REAL4_EXPR*>(this->coords_);
            retval += "def REAL4.EXPR" + case_coords->toString() + " : ^ := "
             + " %_ ";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
    }
    

    return retval;
}
                

REALMATRIX_LITERAL::REALMATRIX_LITERAL(coords::REALMATRIX_LITERAL* c, domain::DomainObject* d) : REALMATRIX_EXPR(c,d) {}
                    
std::string REALMATRIX_LITERAL::toString() const {
    std::string retval = "";
    bool found = false;
    
    //  ret += "(";
    //ret += "def var_" + std::to_string(++index) + ":= 1";
    if(auto dc = dynamic_cast<domain::Velocity3Scaling*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::TimeScaling*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scaling*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Velocity3Shear*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::TimeShear*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3Shear*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Velocity3BasisChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::TimeBasisChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3BasisChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::TimeFrameChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3FrameChange*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        std::cout<<"Warning - Calling toString on a production rather than a case\n;";
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Velocity3Scaling*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::TimeScaling*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scaling*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Velocity3Shear*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::TimeShear*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3Shear*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Velocity3BasisChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::TimeBasisChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3BasisChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::TimeFrameChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3FrameChange*>(cont->getValue())){
                found = true;
                std::cout<<"Warning - Calling toString on a production rather than a case\n;";
            }
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
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
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Velocity3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ScalingExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeScaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeScalingExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ScalingExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ShearExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeShear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeShearExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ShearExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3BasisChangeExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeBasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeBasisChangeExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3BasisChangeExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeFrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeFrameChangeExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3FrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3FrameChangeExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Velocity3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ScalingExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeScaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeScalingExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ScalingExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ShearExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeShear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeShearExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ShearExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3BasisChangeExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeBasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeBasisChangeExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3BasisChangeExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeFrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeFrameChangeExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3FrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3FrameChangeExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX.EXPR" + case_coords->toString() + " : ^ := "
             + "(REAL3.EXPR" + operand_1->coords_->toString() + ")"+ "⬝" +"(REAL3.EXPR" + operand_2->coords_->toString() + ")"+ "⬝" +"(REAL3.EXPR" + operand_3->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Velocity3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ScalingExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeScaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeScalingExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ScalingExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ShearExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeShear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeShearExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ShearExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3BasisChangeExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeBasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeBasisChangeExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3BasisChangeExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeFrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeFrameChangeExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3FrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3FrameChangeExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Velocity3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ScalingExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeScaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeScalingExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ScalingExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ShearExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeShear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeShearExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ShearExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3BasisChangeExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeBasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeBasisChangeExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3BasisChangeExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeFrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeFrameChangeExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3FrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3FrameChangeExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ") "+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ") ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX.EXPR" + case_coords->toString() + " : ^ := "
             + "(REAL1.EXPR" + operand_1->coords_->toString() + ")"+ "⬝" +"(REAL1.EXPR" + operand_2->coords_->toString() + ")"+ "⬝" +"(REAL1.EXPR" + operand_3->coords_->toString() + ")"+ "⬝" +"(REAL1.EXPR" + operand_4->coords_->toString() + ")"+ "⬝" +"(REAL1.EXPR" + operand_5->coords_->toString() + ")"+ "⬝" +"(REAL1.EXPR" + operand_6->coords_->toString() + ")"+ "⬝" +"(REAL1.EXPR" + operand_7->coords_->toString() + ")"+ "⬝" +"(REAL1.EXPR" + operand_8->coords_->toString() + ")"+ "⬝" +"(REAL1.EXPR" + operand_9->coords_->toString() + ")";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
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
    if(auto dc = dynamic_cast<domain::Velocity3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ScalingExpression " +  " := "
             + " ⬝(Velocity3ScalingDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeScaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeScalingExpression " +  " := "
             + " ⬝(TimeScalingDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Scaling*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ScalingExpression " +  " := "
             + " ⬝(Geometric3ScalingDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ShearExpression " +  " := "
             + " ⬝(Velocity3ShearDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeShear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeShearExpression " +  " := "
             + " ⬝(TimeShearDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Shear*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ShearExpression " +  " := "
             + " ⬝(Geometric3ShearDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Velocity3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3BasisChangeExpression " +  " := "
             + " ⬝(Velocity3BasisChangeDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeBasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeBasisChangeExpression " +  " := "
             + " ⬝(TimeBasisChangeDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3BasisChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3BasisChangeExpression " +  " := "
             + " ⬝(Geometric3BasisChangeDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::TimeFrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeFrameChangeExpression " +  " := "
             + " ⬝(TimeFrameChangeDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3FrameChange*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3FrameChangeExpression " +  " := "
             + " ⬝(Geometric3FrameChangeDefault worldGeometry) ";
            //return retval;
    
    }

    if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(this->dom_)){
        found = true;
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " ⬝(Geometric3RotationDefault worldGeometry) ";
            //return retval;
    
    }

    if (auto cont = dynamic_cast<domain::DomainContainer*>(this->dom_)){
        if(cont->hasValue()){

                        
            if(auto dc = dynamic_cast<domain::Velocity3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ScalingExpression " +  " := "
             + " ⬝(Velocity3ScalingDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeScaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeScalingExpression " +  " := "
             + " ⬝(TimeScalingDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Scaling*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ScalingExpression " +  " := "
             + " ⬝(Geometric3ScalingDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3ShearExpression " +  " := "
             + " ⬝(Velocity3ShearDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeShear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeShearExpression " +  " := "
             + " ⬝(TimeShearDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Shear*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3ShearExpression " +  " := "
             + " ⬝(Geometric3ShearDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Velocity3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Velocity3BasisChangeExpression " +  " := "
             + " ⬝(Velocity3BasisChangeDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeBasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeBasisChangeExpression " +  " := "
             + " ⬝(TimeBasisChangeDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3BasisChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3BasisChangeExpression " +  " := "
             + " ⬝(Geometric3BasisChangeDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::TimeFrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : TimeFrameChangeExpression " +  " := "
             + " ⬝(TimeFrameChangeDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3FrameChange*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3FrameChangeExpression " +  " := "
             + " ⬝(Geometric3FrameChangeDefault worldGeometry) ";
            //return retval;
    
            }
            if(auto dc = dynamic_cast<domain::Geometric3Rotation*>(cont->getValue())){
                found = true;
                
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX_EXPR" + case_coords->toString() + " : Geometric3RotationExpression " +  " := "
             + " ⬝(Geometric3RotationDefault worldGeometry) ";
            //return retval;
    
            }
        }
    }

    if(!found){
        //retval = "";
        
            auto case_coords = dynamic_cast<coords::REALMATRIX_EXPR*>(this->coords_);
            retval += "def REALMATRIX.EXPR" + case_coords->toString() + " : ^ := "
             + " ⬝_ ";
            //return retval;
    
    }
    std::replace(retval.begin(), retval.end(), '_', '.');
    int index;
    string sub_str = ": _";
    string singleperiod = ".a";
    while ((index = retval.find(": .")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find(": ^")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, sub_str.length(), sub_str); //remove and replace from that position
    }
    while ((index = retval.find("..")) != string::npos)
    {    //for each location where Hello is found
        retval.replace(index, singleperiod.length(), singleperiod); //remove and replace from that position
    }
    

    return retval;
}
                
} // namespace coords