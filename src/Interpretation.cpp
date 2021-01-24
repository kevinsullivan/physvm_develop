
/*
Establish interpretations for AST nodes:

-  get any required information from oracle 
-  create coordinates for object
-  update ast-coord bijections
-  create corresponding domain object
-  update coord-domain bijection
-  create element-wise inter object
-  update maps: coords-interp, interp-domain
*/

// TODO: These two can be integrated
#include "Coords.h"
#include "Interpretation.h"
#include "Interp.h"
#include "CoordsToInterp.h"
#include "CoordsToDomain.h"
#include "InterpToDomain.h"
#include "ASTToCoords.h"
#include "Oracle_AskAll.h"    // default oracle
//#include "Space.h"
#include "Checker.h"

//#include <g3log/g3log.hpp>
#include <unordered_map>
#include <memory>
#include <vector>
using namespace interp;


std::vector<string> *choice_buffer;

Interpretation::Interpretation() { 
    domain_ = new domain::Domain();
    oracle_ = new oracle::Oracle_AskAll(domain_); 
    choice_buffer = new std::vector<string>();
    oracle_->choice_buffer = choice_buffer;
    /* 
    context_ can only be set later, once Clang starts parse
    */
    ast2coords_ = new ast2coords::ASTToCoords(); 
    coords2dom_ = new coords2domain::CoordsToDomain();
    coords2interp_ = new coords2interp::CoordsToInterp();
    interp2domain_ = new interp2domain::InterpToDomain();
    checker_ = new Checker(this);
}

std::string Interpretation::toString_AST(){
    //this should technically be in Interp but OKAY this second
    std::string math = "";

    math += "import .lang.imperative_DSL.physlang\n\n";
    math += "noncomputable theory\n\n";
            math += "def " + interp::getEnvName() + " := environment.init_env";
            //math += interp->toString_Spaces();
            //math += interp->toString_PROGRAMs();
            //math += this->toString_COMPOUND_STMTs();
            std::vector<interp::MAIN_FUNC_DECL_STMT*> interps;
            for(auto coord : this->MAIN_FUNC_DECL_STMT_vec){
                interps.push_back(this->coords2interp_->getMAIN_FUNC_DECL_STMT(coord));
            }
            for(auto interp_ : interps){
                if(auto dc = dynamic_cast<interp::COMPOUND_STMT*>(interp_->getOperand1())){
                    math += "\n" + dc->toStringLinked(
                        this->getSpaceInterps(), 
                        this->getSpaceNames(), 
                        this->getMSInterps(), this->getMSNames(),  
                        this->getAxisInterps(), this->getAxisNames(),   
                        this->getFrameInterps(), this->getFrameNames(), interp2domain_, true) + "\n";
                }
            }
                
            return math;
        };




void Interpretation::mkSEQ_GLOBALSTMT(const ast::SEQ_GLOBALSTMT * ast , std::vector <ast::GLOBALSTMT*> operands) {
//const ast::COMPOUND_STMT * ast , std::vector < ast::STMT *> operands 
	//coords::GLOBALSTMT* operand1_coords = static_cast<coords::GLOBALSTMT*>(ast2coords_->getDeclCoords(operands));

    vector<coords::GLOBALSTMT*> operand_coords;

    for(auto op : operands)
    {
        
        if(ast2coords_->existsDeclCoords(op)){
            operand_coords.push_back(static_cast<coords::GLOBALSTMT*>(ast2coords_->getDeclCoords(op)));
        } 
    }

    coords::SEQ_GLOBALSTMT* coords = ast2coords_->mkSEQ_GLOBALSTMT(ast, context_ ,operand_coords);

	//domain::DomainObject* operand1_dom = coords2dom_->getGLOBALSTMT(operand_coords);

    vector<domain::DomainObject*> operand_domain;

    for(auto op : operand_coords)
    {
        operand_domain.push_back(coords2dom_->getGLOBALSTMT(op));
    }

    domain::DomainObject* dom = domain_->mkDefaultDomainContainer(operand_domain);
    coords2dom_->putSEQ_GLOBALSTMT(coords, dom);

	//interp::GLOBALSTMT* operand1_interp = coords2interp_->getGLOBALSTMT(operand1_coords);

    vector<interp::GLOBALSTMT*> operand_interp;

    for(auto op : operand_coords)
    {
        //auto p = coords2interp_->getGLOBALSTMT(op);
        operand_interp.push_back(coords2interp_->getGLOBALSTMT(op));
    }

    interp::SEQ_GLOBALSTMT* interp = new interp::SEQ_GLOBALSTMT(coords, dom, operand_interp);
    coords2interp_->putSEQ_GLOBALSTMT(coords, interp);
    interp2domain_->putSEQ_GLOBALSTMT(interp, dom); 
	this->PROGRAM_vec.push_back(coords);
	this->SEQ_GLOBALSTMT_vec.push_back(coords);
};


 std::string Interpretation::toString_SEQ_GLOBALSTMTs(){ 
    std::vector<interp::SEQ_GLOBALSTMT*> interps;
    for(auto coord : this->SEQ_GLOBALSTMT_vec){
        interps.push_back((interp::SEQ_GLOBALSTMT*)this->coords2interp_->getPROGRAM(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toStringLinked(
            this->getSpaceInterps(), 
            this->getSpaceNames(), 
            this->getMSInterps(), this->getMSNames(),  
            this->getAxisInterps(), this->getAxisNames(),   
            this->getFrameInterps(), this->getFrameNames(), interp2domain_, true) + "\n";

    }
    return retval;
}

 std::string Interpretation::toString_PROGRAMs(){ 
    std::vector<interp::PROGRAM*> interps;
    for(auto coord : this->PROGRAM_vec){
        interps.push_back(this->coords2interp_->getPROGRAM(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}

 std::string Interpretation::toString_GLOBALSTMTs(){ 
    std::vector<interp::GLOBALSTMT*> interps;
    for(auto coord : this->GLOBALSTMT_vec){
        interps.push_back(this->coords2interp_->getGLOBALSTMT(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}


void Interpretation::mkCOMPOUND_STMT(const ast::COMPOUND_STMT * ast , std::vector <ast::STMT*> operands) {
//const ast::COMPOUND_STMT * ast , std::vector < ast::STMT *> operands 
	//coords::STMT* operand1_coords = static_cast<coords::STMT*>(ast2coords_->getStmtCoords(operands));

    vector<coords::STMT*> operand_coords;

    for(auto op : operands)
    {
        
        if(ast2coords_->existsStmtCoords(op)){
            operand_coords.push_back(static_cast<coords::STMT*>(ast2coords_->getStmtCoords(op)));
        } 
    }

    coords::COMPOUND_STMT* coords = ast2coords_->mkCOMPOUND_STMT(ast, context_ ,operand_coords);

	//domain::DomainObject* operand1_dom = coords2dom_->getSTMT(operand_coords);

    vector<domain::DomainObject*> operand_domain;

    for(auto op : operand_coords)
    {
        operand_domain.push_back(coords2dom_->getSTMT(op));
    }

    domain::DomainObject* dom = domain_->mkDefaultDomainContainer(operand_domain);
    coords2dom_->putCOMPOUND_STMT(coords, dom);

	//interp::STMT* operand1_interp = coords2interp_->getSTMT(operand1_coords);

    vector<interp::STMT*> operand_interp;

    for(auto op : operand_coords)
    {
        //auto p = coords2interp_->getSTMT(op);
        operand_interp.push_back(coords2interp_->getSTMT(op));
    }

    interp::COMPOUND_STMT* interp = new interp::COMPOUND_STMT(coords, dom, operand_interp);
    coords2interp_->putCOMPOUND_STMT(coords, interp);
    interp2domain_->putCOMPOUND_STMT(interp, dom); 
	this->STMT_vec.push_back(coords);
	this->COMPOUND_STMT_vec.push_back(coords);
};


 std::string Interpretation::toString_COMPOUND_STMTs(){ 
    std::vector<interp::COMPOUND_STMT*> interps;
    for(auto coord : this->COMPOUND_STMT_vec){
        interps.push_back((interp::COMPOUND_STMT*)this->coords2interp_->getSTMT(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toStringLinked(
            this->getSpaceInterps(), 
            this->getSpaceNames(), 
            this->getMSInterps(), this->getMSNames(),  
            this->getAxisInterps(), this->getAxisNames(),   
            this->getFrameInterps(), this->getFrameNames(), interp2domain_, true) + "\n";

    }
    return retval;
}

 std::string Interpretation::toString_STMTs(){ 
    std::vector<interp::STMT*> interps;
    for(auto coord : this->STMT_vec){
        interps.push_back(this->coords2interp_->getSTMT(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}

 std::string Interpretation::toString_FUNC_DECLs(){ 
    std::vector<interp::FUNC_DECL*> interps;
    for(auto coord : this->FUNC_DECL_vec){
        interps.push_back(this->coords2interp_->getFUNC_DECL(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkVOID_FUNC_DECL_STMT(const ast::VOID_FUNC_DECL_STMT * ast ,ast::STMT* operand1) {

	coords::STMT* operand1_coords = static_cast<coords::STMT*>(ast2coords_->getStmtCoords(operand1));

    coords::VOID_FUNC_DECL_STMT* coords = ast2coords_->mkVOID_FUNC_DECL_STMT(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getSTMT(operand1_coords);
    domain::DomainObject* dom = domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putVOID_FUNC_DECL_STMT(coords, dom);

	interp::STMT* operand1_interp = coords2interp_->getSTMT(operand1_coords);

    interp::VOID_FUNC_DECL_STMT* interp = new interp::VOID_FUNC_DECL_STMT(coords, dom, operand1_interp);
    coords2interp_->putVOID_FUNC_DECL_STMT(coords, interp);
    interp2domain_->putVOID_FUNC_DECL_STMT(interp, dom); 
	this->VOID_FUNC_DECL_STMT_vec.push_back(coords);

} 


 std::string Interpretation::toString_VOID_FUNC_DECL_STMTs(){ 
    std::vector<interp::VOID_FUNC_DECL_STMT*> interps;
    for(auto coord : this->VOID_FUNC_DECL_STMT_vec){
        interps.push_back(this->coords2interp_->getVOID_FUNC_DECL_STMT(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkMAIN_FUNC_DECL_STMT(const ast::MAIN_FUNC_DECL_STMT * ast ,ast::STMT* operand1) {

	coords::STMT* operand1_coords = static_cast<coords::STMT*>(ast2coords_->getStmtCoords(operand1));

    coords::MAIN_FUNC_DECL_STMT* coords = ast2coords_->mkMAIN_FUNC_DECL_STMT(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getSTMT(operand1_coords);
    domain::DomainObject* dom = domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putMAIN_FUNC_DECL_STMT(coords, dom);

	interp::STMT* operand1_interp = coords2interp_->getSTMT(operand1_coords);

    interp::MAIN_FUNC_DECL_STMT* interp = new interp::MAIN_FUNC_DECL_STMT(coords, dom, operand1_interp);
    coords2interp_->putMAIN_FUNC_DECL_STMT(coords, interp);
    interp2domain_->putMAIN_FUNC_DECL_STMT(interp, dom); 
	this->MAIN_FUNC_DECL_STMT_vec.push_back(coords);

} 


 std::string Interpretation::toString_MAIN_FUNC_DECL_STMTs(){ 
    std::vector<interp::MAIN_FUNC_DECL_STMT*> interps;
    for(auto coord : this->MAIN_FUNC_DECL_STMT_vec){
        interps.push_back(this->coords2interp_->getMAIN_FUNC_DECL_STMT(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkWHILE_BOOL_EXPR_STMT(const ast::WHILE_BOOL_EXPR_STMT * ast ,ast::BOOL_EXPR* operand1,ast::STMT* operand2) {

	coords::BOOL_EXPR* operand1_coords = static_cast<coords::BOOL_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::STMT* operand2_coords = static_cast<coords::STMT*>(ast2coords_->getStmtCoords(operand2));

    coords::WHILE_BOOL_EXPR_STMT* coords = ast2coords_->mkWHILE_BOOL_EXPR_STMT(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getBOOL_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getSTMT(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putWHILE_BOOL_EXPR_STMT(coords, dom);

	interp::BOOL_EXPR* operand1_interp = coords2interp_->getBOOL_EXPR(operand1_coords);;
	interp::STMT* operand2_interp = coords2interp_->getSTMT(operand2_coords);

    interp::WHILE_BOOL_EXPR_STMT* interp = new interp::WHILE_BOOL_EXPR_STMT(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putWHILE_BOOL_EXPR_STMT(coords, interp);
    interp2domain_->putWHILE_BOOL_EXPR_STMT(interp, dom); 
	this->WHILE_vec.push_back(coords);

} 


 std::string Interpretation::toString_WHILEs(){ 
    std::vector<interp::WHILE*> interps;
    for(auto coord : this->WHILE_vec){
        interps.push_back(this->coords2interp_->getWHILE(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkTRY_STMT(const ast::TRY_STMT * ast ,ast::STMT* operand1) {

	coords::STMT* operand1_coords = static_cast<coords::STMT*>(ast2coords_->getStmtCoords(operand1));

    coords::TRY_STMT* coords = ast2coords_->mkTRY_STMT(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getSTMT(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putTRY_STMT(coords, dom);

	interp::STMT* operand1_interp = coords2interp_->getSTMT(operand1_coords);

    interp::TRY_STMT* interp = new interp::TRY_STMT(coords, dom, operand1_interp);
    coords2interp_->putTRY_STMT(coords, interp);
    interp2domain_->putTRY_STMT(interp, dom); 
	this->TRY_vec.push_back(coords);

} 


 std::string Interpretation::toString_TRYs(){ 
    std::vector<interp::TRY*> interps;
    for(auto coord : this->TRY_vec){
        interps.push_back(this->coords2interp_->getTRY(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkDECL_REAL1_VAR_REAL1_EXPR(const ast::DECL_REAL1_VAR_REAL1_EXPR * ast ,ast::REAL1_VAR_IDENT* operand1,ast::REAL1_EXPR* operand2) {

	coords::REAL1_VAR_IDENT* operand1_coords = static_cast<coords::REAL1_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));;
	coords::REAL1_EXPR* operand2_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::DECL_REAL1_VAR_REAL1_EXPR* coords = ast2coords_->mkDECL_REAL1_VAR_REAL1_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL1_VAR_IDENT(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL1_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putDECL_REAL1_VAR_REAL1_EXPR(coords, dom);

	interp::REAL1_VAR_IDENT* operand1_interp = coords2interp_->getREAL1_VAR_IDENT(operand1_coords);;
	interp::REAL1_EXPR* operand2_interp = coords2interp_->getREAL1_EXPR(operand2_coords);

    interp::DECL_REAL1_VAR_REAL1_EXPR* interp = new interp::DECL_REAL1_VAR_REAL1_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putDECL_REAL1_VAR_REAL1_EXPR(coords, interp);
    interp2domain_->putDECL_REAL1_VAR_REAL1_EXPR(interp, dom); 
	this->DECLARE_vec.push_back(coords);

} 

void Interpretation::mkDECL_REAL3_VAR_REAL3_EXPR(const ast::DECL_REAL3_VAR_REAL3_EXPR * ast ,ast::REAL3_VAR_IDENT* operand1,ast::REAL3_EXPR* operand2) {

	coords::REAL3_VAR_IDENT* operand1_coords = static_cast<coords::REAL3_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));;
	coords::REAL3_EXPR* operand2_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::DECL_REAL3_VAR_REAL3_EXPR* coords = ast2coords_->mkDECL_REAL3_VAR_REAL3_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL3_VAR_IDENT(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL3_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putDECL_REAL3_VAR_REAL3_EXPR(coords, dom);

	interp::REAL3_VAR_IDENT* operand1_interp = coords2interp_->getREAL3_VAR_IDENT(operand1_coords);;
	interp::REAL3_EXPR* operand2_interp = coords2interp_->getREAL3_EXPR(operand2_coords);

    interp::DECL_REAL3_VAR_REAL3_EXPR* interp = new interp::DECL_REAL3_VAR_REAL3_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putDECL_REAL3_VAR_REAL3_EXPR(coords, interp);
    interp2domain_->putDECL_REAL3_VAR_REAL3_EXPR(interp, dom); 
	this->DECLARE_vec.push_back(coords);

} 

void Interpretation::mkDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(const ast::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR * ast ,ast::REALMATRIX4_VAR_IDENT* operand1,ast::REALMATRIX4_EXPR* operand2) {

	coords::REALMATRIX4_VAR_IDENT* operand1_coords = static_cast<coords::REALMATRIX4_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));;
	coords::REALMATRIX4_EXPR* operand2_coords = static_cast<coords::REALMATRIX4_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* coords = ast2coords_->mkDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREALMATRIX4_VAR_IDENT(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREALMATRIX4_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords, dom);

	interp::REALMATRIX4_VAR_IDENT* operand1_interp = coords2interp_->getREALMATRIX4_VAR_IDENT(operand1_coords);;
	interp::REALMATRIX4_EXPR* operand2_interp = coords2interp_->getREALMATRIX4_EXPR(operand2_coords);

    interp::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* interp = new interp::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords, interp);
    interp2domain_->putDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(interp, dom); 
	this->DECLARE_vec.push_back(coords);

} 

void Interpretation::mkDECL_REAL4_VAR_REAL4_EXPR(const ast::DECL_REAL4_VAR_REAL4_EXPR * ast ,ast::REAL4_VAR_IDENT* operand1,ast::REAL4_EXPR* operand2) {

	coords::REAL4_VAR_IDENT* operand1_coords = static_cast<coords::REAL4_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));;
	coords::REAL4_EXPR* operand2_coords = static_cast<coords::REAL4_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::DECL_REAL4_VAR_REAL4_EXPR* coords = ast2coords_->mkDECL_REAL4_VAR_REAL4_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL4_VAR_IDENT(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL4_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putDECL_REAL4_VAR_REAL4_EXPR(coords, dom);

	interp::REAL4_VAR_IDENT* operand1_interp = coords2interp_->getREAL4_VAR_IDENT(operand1_coords);;
	interp::REAL4_EXPR* operand2_interp = coords2interp_->getREAL4_EXPR(operand2_coords);

    interp::DECL_REAL4_VAR_REAL4_EXPR* interp = new interp::DECL_REAL4_VAR_REAL4_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putDECL_REAL4_VAR_REAL4_EXPR(coords, interp);
    interp2domain_->putDECL_REAL4_VAR_REAL4_EXPR(interp, dom); 
	this->DECLARE_vec.push_back(coords);

} 

void Interpretation::mkDECL_BOOL_VAR_BOOL_EXPR(const ast::DECL_BOOL_VAR_BOOL_EXPR * ast ,ast::BOOL_VAR_IDENT* operand1,ast::BOOL_EXPR* operand2) {

	coords::BOOL_VAR_IDENT* operand1_coords = static_cast<coords::BOOL_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));;
	coords::BOOL_EXPR* operand2_coords = static_cast<coords::BOOL_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::DECL_BOOL_VAR_BOOL_EXPR* coords = ast2coords_->mkDECL_BOOL_VAR_BOOL_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getBOOL_VAR_IDENT(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getBOOL_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putDECL_BOOL_VAR_BOOL_EXPR(coords, dom);

	interp::BOOL_VAR_IDENT* operand1_interp = coords2interp_->getBOOL_VAR_IDENT(operand1_coords);;
	interp::BOOL_EXPR* operand2_interp = coords2interp_->getBOOL_EXPR(operand2_coords);

    interp::DECL_BOOL_VAR_BOOL_EXPR* interp = new interp::DECL_BOOL_VAR_BOOL_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putDECL_BOOL_VAR_BOOL_EXPR(coords, interp);
    interp2domain_->putDECL_BOOL_VAR_BOOL_EXPR(interp, dom); 
	this->DECLARE_vec.push_back(coords);

} 

void Interpretation::mkDECL_REAL1_VAR(const ast::DECL_REAL1_VAR * ast ,ast::REAL1_VAR_IDENT* operand1) {

	coords::REAL1_VAR_IDENT* operand1_coords = static_cast<coords::REAL1_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));

    coords::DECL_REAL1_VAR* coords = ast2coords_->mkDECL_REAL1_VAR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL1_VAR_IDENT(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putDECL_REAL1_VAR(coords, dom);

	interp::REAL1_VAR_IDENT* operand1_interp = coords2interp_->getREAL1_VAR_IDENT(operand1_coords);

    interp::DECL_REAL1_VAR* interp = new interp::DECL_REAL1_VAR(coords, dom, operand1_interp);
    coords2interp_->putDECL_REAL1_VAR(coords, interp);
    interp2domain_->putDECL_REAL1_VAR(interp, dom); 
	this->DECLARE_vec.push_back(coords);

} 

void Interpretation::mkDECL_REAL3_VAR(const ast::DECL_REAL3_VAR * ast ,ast::REAL3_VAR_IDENT* operand1) {

	coords::REAL3_VAR_IDENT* operand1_coords = static_cast<coords::REAL3_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));

    coords::DECL_REAL3_VAR* coords = ast2coords_->mkDECL_REAL3_VAR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL3_VAR_IDENT(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putDECL_REAL3_VAR(coords, dom);

	interp::REAL3_VAR_IDENT* operand1_interp = coords2interp_->getREAL3_VAR_IDENT(operand1_coords);

    interp::DECL_REAL3_VAR* interp = new interp::DECL_REAL3_VAR(coords, dom, operand1_interp);
    coords2interp_->putDECL_REAL3_VAR(coords, interp);
    interp2domain_->putDECL_REAL3_VAR(interp, dom); 
	this->DECLARE_vec.push_back(coords);

} 

void Interpretation::mkDECL_REALMATRIX4_VAR(const ast::DECL_REALMATRIX4_VAR * ast ,ast::REALMATRIX4_VAR_IDENT* operand1) {

	coords::REALMATRIX4_VAR_IDENT* operand1_coords = static_cast<coords::REALMATRIX4_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));

    coords::DECL_REALMATRIX4_VAR* coords = ast2coords_->mkDECL_REALMATRIX4_VAR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREALMATRIX4_VAR_IDENT(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putDECL_REALMATRIX4_VAR(coords, dom);

	interp::REALMATRIX4_VAR_IDENT* operand1_interp = coords2interp_->getREALMATRIX4_VAR_IDENT(operand1_coords);

    interp::DECL_REALMATRIX4_VAR* interp = new interp::DECL_REALMATRIX4_VAR(coords, dom, operand1_interp);
    coords2interp_->putDECL_REALMATRIX4_VAR(coords, interp);
    interp2domain_->putDECL_REALMATRIX4_VAR(interp, dom); 
	this->DECLARE_vec.push_back(coords);

} 

void Interpretation::mkDECL_REAL4_VAR(const ast::DECL_REAL4_VAR * ast ,ast::REAL4_VAR_IDENT* operand1) {

	coords::REAL4_VAR_IDENT* operand1_coords = static_cast<coords::REAL4_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));

    coords::DECL_REAL4_VAR* coords = ast2coords_->mkDECL_REAL4_VAR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL4_VAR_IDENT(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putDECL_REAL4_VAR(coords, dom);

	interp::REAL4_VAR_IDENT* operand1_interp = coords2interp_->getREAL4_VAR_IDENT(operand1_coords);

    interp::DECL_REAL4_VAR* interp = new interp::DECL_REAL4_VAR(coords, dom, operand1_interp);
    coords2interp_->putDECL_REAL4_VAR(coords, interp);
    interp2domain_->putDECL_REAL4_VAR(interp, dom); 
	this->DECLARE_vec.push_back(coords);

} 

void Interpretation::mkDECL_BOOL_VAR(const ast::DECL_BOOL_VAR * ast ,ast::BOOL_VAR_IDENT* operand1) {

	coords::BOOL_VAR_IDENT* operand1_coords = static_cast<coords::BOOL_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));

    coords::DECL_BOOL_VAR* coords = ast2coords_->mkDECL_BOOL_VAR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getBOOL_VAR_IDENT(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putDECL_BOOL_VAR(coords, dom);

	interp::BOOL_VAR_IDENT* operand1_interp = coords2interp_->getBOOL_VAR_IDENT(operand1_coords);

    interp::DECL_BOOL_VAR* interp = new interp::DECL_BOOL_VAR(coords, dom, operand1_interp);
    coords2interp_->putDECL_BOOL_VAR(coords, interp);
    interp2domain_->putDECL_BOOL_VAR(interp, dom); 
	this->DECLARE_vec.push_back(coords);

} 


 std::string Interpretation::toString_DECLAREs(){ 
    std::vector<interp::DECLARE*> interps;
    for(auto coord : this->DECLARE_vec){
        interps.push_back(this->coords2interp_->getDECLARE(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkASNR1_REAL1_VAR_REAL1_EXPR(const ast::ASNR1_REAL1_VAR_REAL1_EXPR * ast ,ast::REAL1_VAR_IDENT* operand1,ast::REAL1_EXPR* operand2) {

	coords::REAL1_VAR_IDENT* operand1_coords = static_cast<coords::REAL1_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));;
	coords::REAL1_EXPR* operand2_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::ASNR1_REAL1_VAR_REAL1_EXPR* coords = ast2coords_->mkASNR1_REAL1_VAR_REAL1_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL1_VAR_IDENT(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL1_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putASNR1_REAL1_VAR_REAL1_EXPR(coords, dom);

	interp::REAL1_VAR_IDENT* operand1_interp = coords2interp_->getREAL1_VAR_IDENT(operand1_coords);;
	interp::REAL1_EXPR* operand2_interp = coords2interp_->getREAL1_EXPR(operand2_coords);

    interp::ASNR1_REAL1_VAR_REAL1_EXPR* interp = new interp::ASNR1_REAL1_VAR_REAL1_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putASNR1_REAL1_VAR_REAL1_EXPR(coords, interp);
    interp2domain_->putASNR1_REAL1_VAR_REAL1_EXPR(interp, dom); 
	this->ASSIGN_vec.push_back(coords);

} 

void Interpretation::mkASNR3_REAL3_VAR_REAL3_EXPR(const ast::ASNR3_REAL3_VAR_REAL3_EXPR * ast ,ast::REAL3_VAR_IDENT* operand1,ast::REAL3_EXPR* operand2) {

	coords::REAL3_VAR_IDENT* operand1_coords = static_cast<coords::REAL3_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));;
	coords::REAL3_EXPR* operand2_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::ASNR3_REAL3_VAR_REAL3_EXPR* coords = ast2coords_->mkASNR3_REAL3_VAR_REAL3_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL3_VAR_IDENT(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL3_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putASNR3_REAL3_VAR_REAL3_EXPR(coords, dom);

	interp::REAL3_VAR_IDENT* operand1_interp = coords2interp_->getREAL3_VAR_IDENT(operand1_coords);;
	interp::REAL3_EXPR* operand2_interp = coords2interp_->getREAL3_EXPR(operand2_coords);

    interp::ASNR3_REAL3_VAR_REAL3_EXPR* interp = new interp::ASNR3_REAL3_VAR_REAL3_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putASNR3_REAL3_VAR_REAL3_EXPR(coords, interp);
    interp2domain_->putASNR3_REAL3_VAR_REAL3_EXPR(interp, dom); 
	this->ASSIGN_vec.push_back(coords);

} 

void Interpretation::mkASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(const ast::ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR * ast ,ast::REALMATRIX4_VAR_IDENT* operand1,ast::REALMATRIX4_EXPR* operand2) {

	coords::REALMATRIX4_VAR_IDENT* operand1_coords = static_cast<coords::REALMATRIX4_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));;
	coords::REALMATRIX4_EXPR* operand2_coords = static_cast<coords::REALMATRIX4_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR* coords = ast2coords_->mkASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREALMATRIX4_VAR_IDENT(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREALMATRIX4_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords, dom);

	interp::REALMATRIX4_VAR_IDENT* operand1_interp = coords2interp_->getREALMATRIX4_VAR_IDENT(operand1_coords);;
	interp::REALMATRIX4_EXPR* operand2_interp = coords2interp_->getREALMATRIX4_EXPR(operand2_coords);

    interp::ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR* interp = new interp::ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords, interp);
    interp2domain_->putASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(interp, dom); 
	this->ASSIGN_vec.push_back(coords);

} 


 std::string Interpretation::toString_ASSIGNs(){ 
    std::vector<interp::ASSIGN*> interps;
    for(auto coord : this->ASSIGN_vec){
        interps.push_back(this->coords2interp_->getASSIGN(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}

 std::string Interpretation::toString_REXPRs(){ 
    std::vector<interp::REXPR*> interps;
    for(auto coord : this->REXPR_vec){
        interps.push_back(this->coords2interp_->getREXPR(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}

 std::string Interpretation::toString_LEXPRs(){ 
    std::vector<interp::LEXPR*> interps;
    for(auto coord : this->LEXPR_vec){
        interps.push_back(this->coords2interp_->getLEXPR(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkREF_BOOL_VAR(const ast::REF_BOOL_VAR * ast ,ast::BOOL_VAR_IDENT* operand1,std::shared_ptr<bool> value0) {

	coords::BOOL_VAR_IDENT* operand1_coords = static_cast<coords::BOOL_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));

    coords::REF_BOOL_VAR* coords = ast2coords_->mkREF_BOOL_VAR(ast, context_ ,operand1_coords,value0);

	domain::DomainObject* operand1_dom = coords2dom_->getBOOL_VAR_IDENT(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putREF_BOOL_VAR(coords, dom);

	interp::BOOL_VAR_IDENT* operand1_interp = coords2interp_->getBOOL_VAR_IDENT(operand1_coords);

    interp::REF_BOOL_VAR* interp = new interp::REF_BOOL_VAR(coords, dom, operand1_interp);
    coords2interp_->putREF_BOOL_VAR(coords, interp);
    interp2domain_->putREF_BOOL_VAR(interp, dom); 
	this->BOOL_EXPR_vec.push_back(coords);

} 


 std::string Interpretation::toString_BOOL_EXPRs(){ 
    std::vector<interp::BOOL_EXPR*> interps;
    for(auto coord : this->BOOL_EXPR_vec){
        interps.push_back(this->coords2interp_->getBOOL_EXPR(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkREF_REALMATRIX4_VAR(const ast::REF_REALMATRIX4_VAR * ast ,ast::REALMATRIX4_VAR_IDENT* operand1) {

	coords::REALMATRIX4_VAR_IDENT* operand1_coords = static_cast<coords::REALMATRIX4_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));

    coords::REF_REALMATRIX4_VAR* coords = ast2coords_->mkREF_REALMATRIX4_VAR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREALMATRIX4_VAR_IDENT(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putREF_REALMATRIX4_VAR(coords, dom);

	interp::REALMATRIX4_VAR_IDENT* operand1_interp = coords2interp_->getREALMATRIX4_VAR_IDENT(operand1_coords);

    interp::REF_REALMATRIX4_VAR* interp = new interp::REF_REALMATRIX4_VAR(coords, dom, operand1_interp);
    coords2interp_->putREF_REALMATRIX4_VAR(coords, interp);
    interp2domain_->putREF_REALMATRIX4_VAR(interp, dom); 
	this->REALMATRIX4_EXPR_vec.push_back(coords);

} 

void Interpretation::mkMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(const ast::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR * ast ,ast::REALMATRIX4_EXPR* operand1,ast::REALMATRIX4_EXPR* operand2) {

	coords::REALMATRIX4_EXPR* operand1_coords = static_cast<coords::REALMATRIX4_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REALMATRIX4_EXPR* operand2_coords = static_cast<coords::REALMATRIX4_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* coords = ast2coords_->mkMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREALMATRIX4_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREALMATRIX4_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(coords, dom);

	interp::REALMATRIX4_EXPR* operand1_interp = coords2interp_->getREALMATRIX4_EXPR(operand1_coords);;
	interp::REALMATRIX4_EXPR* operand2_interp = coords2interp_->getREALMATRIX4_EXPR(operand2_coords);

    interp::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* interp = new interp::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(coords, interp);
    interp2domain_->putMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(interp, dom); 
	this->REALMATRIX4_EXPR_vec.push_back(coords);

} 


 std::string Interpretation::toString_REALMATRIX4_EXPRs(){ 
    std::vector<interp::REALMATRIX4_EXPR*> interps;
    for(auto coord : this->REALMATRIX4_EXPR_vec){
        interps.push_back(this->coords2interp_->getREALMATRIX4_EXPR(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkREF_REAL4_VAR(const ast::REF_REAL4_VAR * ast ,ast::REAL4_VAR_IDENT* operand1,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2,std::shared_ptr<float> value3) {

	coords::REAL4_VAR_IDENT* operand1_coords = static_cast<coords::REAL4_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));

    coords::REF_REAL4_VAR* coords = ast2coords_->mkREF_REAL4_VAR(ast, context_ ,operand1_coords,value0,value1,value2,value3);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL4_VAR_IDENT(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putREF_REAL4_VAR(coords, dom);

	interp::REAL4_VAR_IDENT* operand1_interp = coords2interp_->getREAL4_VAR_IDENT(operand1_coords);

    interp::REF_REAL4_VAR* interp = new interp::REF_REAL4_VAR(coords, dom, operand1_interp);
    coords2interp_->putREF_REAL4_VAR(coords, interp);
    interp2domain_->putREF_REAL4_VAR(interp, dom); 
	this->REAL4_EXPR_vec.push_back(coords);

} 

void Interpretation::mkADD_REAL4_EXPR_REAL4_EXPR(const ast::ADD_REAL4_EXPR_REAL4_EXPR * ast ,ast::REAL4_EXPR* operand1,ast::REAL4_EXPR* operand2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2,std::shared_ptr<float> value3) {

	coords::REAL4_EXPR* operand1_coords = static_cast<coords::REAL4_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL4_EXPR* operand2_coords = static_cast<coords::REAL4_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::ADD_REAL4_EXPR_REAL4_EXPR* coords = ast2coords_->mkADD_REAL4_EXPR_REAL4_EXPR(ast, context_ ,operand1_coords,operand2_coords,value0,value1,value2,value3);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL4_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL4_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putADD_REAL4_EXPR_REAL4_EXPR(coords, dom);

	interp::REAL4_EXPR* operand1_interp = coords2interp_->getREAL4_EXPR(operand1_coords);;
	interp::REAL4_EXPR* operand2_interp = coords2interp_->getREAL4_EXPR(operand2_coords);

    interp::ADD_REAL4_EXPR_REAL4_EXPR* interp = new interp::ADD_REAL4_EXPR_REAL4_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putADD_REAL4_EXPR_REAL4_EXPR(coords, interp);
    interp2domain_->putADD_REAL4_EXPR_REAL4_EXPR(interp, dom); 
	this->REAL4_EXPR_vec.push_back(coords);

} 

void Interpretation::mkMUL_REAL4_EXPR_REAL4_EXPR(const ast::MUL_REAL4_EXPR_REAL4_EXPR * ast ,ast::REAL4_EXPR* operand1,ast::REAL4_EXPR* operand2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2,std::shared_ptr<float> value3) {

	coords::REAL4_EXPR* operand1_coords = static_cast<coords::REAL4_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL4_EXPR* operand2_coords = static_cast<coords::REAL4_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::MUL_REAL4_EXPR_REAL4_EXPR* coords = ast2coords_->mkMUL_REAL4_EXPR_REAL4_EXPR(ast, context_ ,operand1_coords,operand2_coords,value0,value1,value2,value3);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL4_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL4_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putMUL_REAL4_EXPR_REAL4_EXPR(coords, dom);

	interp::REAL4_EXPR* operand1_interp = coords2interp_->getREAL4_EXPR(operand1_coords);;
	interp::REAL4_EXPR* operand2_interp = coords2interp_->getREAL4_EXPR(operand2_coords);

    interp::MUL_REAL4_EXPR_REAL4_EXPR* interp = new interp::MUL_REAL4_EXPR_REAL4_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putMUL_REAL4_EXPR_REAL4_EXPR(coords, interp);
    interp2domain_->putMUL_REAL4_EXPR_REAL4_EXPR(interp, dom); 
	this->REAL4_EXPR_vec.push_back(coords);

} 


 std::string Interpretation::toString_REAL4_EXPRs(){ 
    std::vector<interp::REAL4_EXPR*> interps;
    for(auto coord : this->REAL4_EXPR_vec){
        interps.push_back(this->coords2interp_->getREAL4_EXPR(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkREF_REAL3_VAR(const ast::REF_REAL3_VAR * ast ,ast::REAL3_VAR_IDENT* operand1,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) {

	coords::REAL3_VAR_IDENT* operand1_coords = static_cast<coords::REAL3_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));

    coords::REF_REAL3_VAR* coords = ast2coords_->mkREF_REAL3_VAR(ast, context_ ,operand1_coords,value0,value1,value2);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL3_VAR_IDENT(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putREF_REAL3_VAR(coords, dom);

	interp::REAL3_VAR_IDENT* operand1_interp = coords2interp_->getREAL3_VAR_IDENT(operand1_coords);

    interp::REF_REAL3_VAR* interp = new interp::REF_REAL3_VAR(coords, dom, operand1_interp);
    coords2interp_->putREF_REAL3_VAR(coords, interp);
    interp2domain_->putREF_REAL3_VAR(interp, dom); 
	this->REAL3_EXPR_vec.push_back(coords);

} 

void Interpretation::mkADD_REAL3_EXPR_REAL3_EXPR(const ast::ADD_REAL3_EXPR_REAL3_EXPR * ast ,ast::REAL3_EXPR* operand1,ast::REAL3_EXPR* operand2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) {

	coords::REAL3_EXPR* operand1_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL3_EXPR* operand2_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::ADD_REAL3_EXPR_REAL3_EXPR* coords = ast2coords_->mkADD_REAL3_EXPR_REAL3_EXPR(ast, context_ ,operand1_coords,operand2_coords,value0,value1,value2);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL3_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL3_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putADD_REAL3_EXPR_REAL3_EXPR(coords, dom);

	interp::REAL3_EXPR* operand1_interp = coords2interp_->getREAL3_EXPR(operand1_coords);;
	interp::REAL3_EXPR* operand2_interp = coords2interp_->getREAL3_EXPR(operand2_coords);

    interp::ADD_REAL3_EXPR_REAL3_EXPR* interp = new interp::ADD_REAL3_EXPR_REAL3_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putADD_REAL3_EXPR_REAL3_EXPR(coords, interp);
    interp2domain_->putADD_REAL3_EXPR_REAL3_EXPR(interp, dom); 
	this->REAL3_EXPR_vec.push_back(coords);

} 

void Interpretation::mkLMUL_REAL1_EXPR_REAL3_EXPR(const ast::LMUL_REAL1_EXPR_REAL3_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL3_EXPR* operand2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) {

	coords::REAL1_EXPR* operand1_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL3_EXPR* operand2_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::LMUL_REAL1_EXPR_REAL3_EXPR* coords = ast2coords_->mkLMUL_REAL1_EXPR_REAL3_EXPR(ast, context_ ,operand1_coords,operand2_coords,value0,value1,value2);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL1_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL3_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putLMUL_REAL1_EXPR_REAL3_EXPR(coords, dom);

	interp::REAL1_EXPR* operand1_interp = coords2interp_->getREAL1_EXPR(operand1_coords);;
	interp::REAL3_EXPR* operand2_interp = coords2interp_->getREAL3_EXPR(operand2_coords);

    interp::LMUL_REAL1_EXPR_REAL3_EXPR* interp = new interp::LMUL_REAL1_EXPR_REAL3_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putLMUL_REAL1_EXPR_REAL3_EXPR(coords, interp);
    interp2domain_->putLMUL_REAL1_EXPR_REAL3_EXPR(interp, dom); 
	this->REAL3_EXPR_vec.push_back(coords);

} 

void Interpretation::mkRMUL_REAL3_EXPR_REAL1_EXPR(const ast::RMUL_REAL3_EXPR_REAL1_EXPR * ast ,ast::REAL3_EXPR* operand1,ast::REAL1_EXPR* operand2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) {

	coords::REAL3_EXPR* operand1_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL1_EXPR* operand2_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::RMUL_REAL3_EXPR_REAL1_EXPR* coords = ast2coords_->mkRMUL_REAL3_EXPR_REAL1_EXPR(ast, context_ ,operand1_coords,operand2_coords,value0,value1,value2);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL3_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL1_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putRMUL_REAL3_EXPR_REAL1_EXPR(coords, dom);

	interp::REAL3_EXPR* operand1_interp = coords2interp_->getREAL3_EXPR(operand1_coords);;
	interp::REAL1_EXPR* operand2_interp = coords2interp_->getREAL1_EXPR(operand2_coords);

    interp::RMUL_REAL3_EXPR_REAL1_EXPR* interp = new interp::RMUL_REAL3_EXPR_REAL1_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putRMUL_REAL3_EXPR_REAL1_EXPR(coords, interp);
    interp2domain_->putRMUL_REAL3_EXPR_REAL1_EXPR(interp, dom); 
	this->REAL3_EXPR_vec.push_back(coords);

} 

void Interpretation::mkTMUL_REALMATRIX4_EXPR_REAL3_EXPR(const ast::TMUL_REALMATRIX4_EXPR_REAL3_EXPR * ast ,ast::REALMATRIX4_EXPR* operand1,ast::REAL3_EXPR* operand2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) {

	coords::REALMATRIX4_EXPR* operand1_coords = static_cast<coords::REALMATRIX4_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL3_EXPR* operand2_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* coords = ast2coords_->mkTMUL_REALMATRIX4_EXPR_REAL3_EXPR(ast, context_ ,operand1_coords,operand2_coords,value0,value1,value2);

	domain::DomainObject* operand1_dom = coords2dom_->getREALMATRIX4_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL3_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putTMUL_REALMATRIX4_EXPR_REAL3_EXPR(coords, dom);

	interp::REALMATRIX4_EXPR* operand1_interp = coords2interp_->getREALMATRIX4_EXPR(operand1_coords);;
	interp::REAL3_EXPR* operand2_interp = coords2interp_->getREAL3_EXPR(operand2_coords);

    interp::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* interp = new interp::TMUL_REALMATRIX4_EXPR_REAL3_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putTMUL_REALMATRIX4_EXPR_REAL3_EXPR(coords, interp);
    interp2domain_->putTMUL_REALMATRIX4_EXPR_REAL3_EXPR(interp, dom); 
	this->REAL3_EXPR_vec.push_back(coords);

} 


 std::string Interpretation::toString_REAL3_EXPRs(){ 
    std::vector<interp::REAL3_EXPR*> interps;
    for(auto coord : this->REAL3_EXPR_vec){
        interps.push_back(this->coords2interp_->getREAL3_EXPR(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkLREF_REAL3_VAR(const ast::LREF_REAL3_VAR * ast ,ast::REAL3_VAR_IDENT* operand1,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) {

	coords::REAL3_VAR_IDENT* operand1_coords = static_cast<coords::REAL3_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));

    coords::LREF_REAL3_VAR* coords = ast2coords_->mkLREF_REAL3_VAR(ast, context_ ,operand1_coords,value0,value1,value2);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL3_VAR_IDENT(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putLREF_REAL3_VAR(coords, dom);

	interp::REAL3_VAR_IDENT* operand1_interp = coords2interp_->getREAL3_VAR_IDENT(operand1_coords);

    interp::LREF_REAL3_VAR* interp = new interp::LREF_REAL3_VAR(coords, dom, operand1_interp);
    coords2interp_->putLREF_REAL3_VAR(coords, interp);
    interp2domain_->putLREF_REAL3_VAR(interp, dom); 
	this->REAL3_LEXPR_vec.push_back(coords);

} 


 std::string Interpretation::toString_REAL3_LEXPRs(){ 
    std::vector<interp::REAL3_LEXPR*> interps;
    for(auto coord : this->REAL3_LEXPR_vec){
        interps.push_back(this->coords2interp_->getREAL3_LEXPR(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkREF_REAL1_VAR(const ast::REF_REAL1_VAR * ast ,ast::REAL1_VAR_IDENT* operand1,std::shared_ptr<float> value0) {

	coords::REAL1_VAR_IDENT* operand1_coords = static_cast<coords::REAL1_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));

    coords::REF_REAL1_VAR* coords = ast2coords_->mkREF_REAL1_VAR(ast, context_ ,operand1_coords,value0);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL1_VAR_IDENT(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putREF_REAL1_VAR(coords, dom);

	interp::REAL1_VAR_IDENT* operand1_interp = coords2interp_->getREAL1_VAR_IDENT(operand1_coords);

    interp::REF_REAL1_VAR* interp = new interp::REF_REAL1_VAR(coords, dom, operand1_interp);
    coords2interp_->putREF_REAL1_VAR(coords, interp);
    interp2domain_->putREF_REAL1_VAR(interp, dom); 
	this->REAL1_EXPR_vec.push_back(coords);

} 

void Interpretation::mkADD_REAL1_EXPR_REAL1_EXPR(const ast::ADD_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2,std::shared_ptr<float> value0) {

	coords::REAL1_EXPR* operand1_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL1_EXPR* operand2_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::ADD_REAL1_EXPR_REAL1_EXPR* coords = ast2coords_->mkADD_REAL1_EXPR_REAL1_EXPR(ast, context_ ,operand1_coords,operand2_coords,value0);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL1_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL1_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putADD_REAL1_EXPR_REAL1_EXPR(coords, dom);

	interp::REAL1_EXPR* operand1_interp = coords2interp_->getREAL1_EXPR(operand1_coords);;
	interp::REAL1_EXPR* operand2_interp = coords2interp_->getREAL1_EXPR(operand2_coords);

    interp::ADD_REAL1_EXPR_REAL1_EXPR* interp = new interp::ADD_REAL1_EXPR_REAL1_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putADD_REAL1_EXPR_REAL1_EXPR(coords, interp);
    interp2domain_->putADD_REAL1_EXPR_REAL1_EXPR(interp, dom); 
	this->REAL1_EXPR_vec.push_back(coords);

} 

void Interpretation::mkMUL_REAL1_EXPR_REAL1_EXPR(const ast::MUL_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2,std::shared_ptr<float> value0) {

	coords::REAL1_EXPR* operand1_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL1_EXPR* operand2_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::MUL_REAL1_EXPR_REAL1_EXPR* coords = ast2coords_->mkMUL_REAL1_EXPR_REAL1_EXPR(ast, context_ ,operand1_coords,operand2_coords,value0);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL1_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL1_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putMUL_REAL1_EXPR_REAL1_EXPR(coords, dom);

	interp::REAL1_EXPR* operand1_interp = coords2interp_->getREAL1_EXPR(operand1_coords);;
	interp::REAL1_EXPR* operand2_interp = coords2interp_->getREAL1_EXPR(operand2_coords);

    interp::MUL_REAL1_EXPR_REAL1_EXPR* interp = new interp::MUL_REAL1_EXPR_REAL1_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putMUL_REAL1_EXPR_REAL1_EXPR(coords, interp);
    interp2domain_->putMUL_REAL1_EXPR_REAL1_EXPR(interp, dom); 
	this->REAL1_EXPR_vec.push_back(coords);

} 


 std::string Interpretation::toString_REAL1_EXPRs(){ 
    std::vector<interp::REAL1_EXPR*> interps;
    for(auto coord : this->REAL1_EXPR_vec){
        interps.push_back(this->coords2interp_->getREAL1_EXPR(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkBOOL_VAR_IDENT(const ast::BOOL_VAR_IDENT * ast ,std::shared_ptr<float> value0) {


    coords::BOOL_VAR_IDENT* coords = ast2coords_->mkBOOL_VAR_IDENT(ast, context_ ,value0);

    domain::DomainObject* dom = domain_->mkDefaultDomainContainer({});
    coords2dom_->putBOOL_VAR_IDENT(coords, dom);


    interp::BOOL_VAR_IDENT* interp = new interp::BOOL_VAR_IDENT(coords, dom);
    coords2interp_->putBOOL_VAR_IDENT(coords, interp);
    interp2domain_->putBOOL_VAR_IDENT(interp, dom); 
	this->BOOL_VAR_IDENT_vec.push_back(coords);

} 


 std::string Interpretation::toString_BOOL_VAR_IDENTs(){ 
    std::vector<interp::BOOL_VAR_IDENT*> interps;
    for(auto coord : this->BOOL_VAR_IDENT_vec){
        interps.push_back(this->coords2interp_->getBOOL_VAR_IDENT(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkREAL1_VAR_IDENT(const ast::REAL1_VAR_IDENT * ast ,std::shared_ptr<float> value0) {


    coords::REAL1_VAR_IDENT* coords = ast2coords_->mkREAL1_VAR_IDENT(ast, context_ ,value0);

    domain::DomainObject* dom = domain_->mkDefaultDomainContainer({});
    coords2dom_->putREAL1_VAR_IDENT(coords, dom);


    interp::REAL1_VAR_IDENT* interp = new interp::REAL1_VAR_IDENT(coords, dom);
    coords2interp_->putREAL1_VAR_IDENT(coords, interp);
    interp2domain_->putREAL1_VAR_IDENT(interp, dom); 
	this->REAL1_VAR_IDENT_vec.push_back(coords);

} 


 std::string Interpretation::toString_REAL1_VAR_IDENTs(){ 
    std::vector<interp::REAL1_VAR_IDENT*> interps;
    for(auto coord : this->REAL1_VAR_IDENT_vec){
        interps.push_back(this->coords2interp_->getREAL1_VAR_IDENT(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkREAL3_VAR_IDENT(const ast::REAL3_VAR_IDENT * ast ,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) {


    coords::REAL3_VAR_IDENT* coords = ast2coords_->mkREAL3_VAR_IDENT(ast, context_ ,value0,value1,value2);

    domain::DomainObject* dom = domain_->mkDefaultDomainContainer({});
    coords2dom_->putREAL3_VAR_IDENT(coords, dom);


    interp::REAL3_VAR_IDENT* interp = new interp::REAL3_VAR_IDENT(coords, dom);
    coords2interp_->putREAL3_VAR_IDENT(coords, interp);
    interp2domain_->putREAL3_VAR_IDENT(interp, dom); 
	this->REAL3_VAR_IDENT_vec.push_back(coords);

} 


 std::string Interpretation::toString_REAL3_VAR_IDENTs(){ 
    std::vector<interp::REAL3_VAR_IDENT*> interps;
    for(auto coord : this->REAL3_VAR_IDENT_vec){
        interps.push_back(this->coords2interp_->getREAL3_VAR_IDENT(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkREAL4_VAR_IDENT(const ast::REAL4_VAR_IDENT * ast ,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2,std::shared_ptr<float> value3) {


    coords::REAL4_VAR_IDENT* coords = ast2coords_->mkREAL4_VAR_IDENT(ast, context_ ,value0,value1,value2,value3);

    domain::DomainObject* dom = domain_->mkDefaultDomainContainer({});
    coords2dom_->putREAL4_VAR_IDENT(coords, dom);


    interp::REAL4_VAR_IDENT* interp = new interp::REAL4_VAR_IDENT(coords, dom);
    coords2interp_->putREAL4_VAR_IDENT(coords, interp);
    interp2domain_->putREAL4_VAR_IDENT(interp, dom); 
	this->REAL4_VAR_IDENT_vec.push_back(coords);

} 


 std::string Interpretation::toString_REAL4_VAR_IDENTs(){ 
    std::vector<interp::REAL4_VAR_IDENT*> interps;
    for(auto coord : this->REAL4_VAR_IDENT_vec){
        interps.push_back(this->coords2interp_->getREAL4_VAR_IDENT(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkREALMATRIX4_VAR_IDENT(const ast::REALMATRIX4_VAR_IDENT * ast ) {


    coords::REALMATRIX4_VAR_IDENT* coords = ast2coords_->mkREALMATRIX4_VAR_IDENT(ast, context_ );

    domain::DomainObject* dom = domain_->mkDefaultDomainContainer({});
    coords2dom_->putREALMATRIX4_VAR_IDENT(coords, dom);


    interp::REALMATRIX4_VAR_IDENT* interp = new interp::REALMATRIX4_VAR_IDENT(coords, dom);
    coords2interp_->putREALMATRIX4_VAR_IDENT(coords, interp);
    interp2domain_->putREALMATRIX4_VAR_IDENT(interp, dom); 
	this->REALMATRIX4_VAR_IDENT_vec.push_back(coords);

} 


 std::string Interpretation::toString_REALMATRIX4_VAR_IDENTs(){ 
    std::vector<interp::REALMATRIX4_VAR_IDENT*> interps;
    for(auto coord : this->REALMATRIX4_VAR_IDENT_vec){
        interps.push_back(this->coords2interp_->getREALMATRIX4_VAR_IDENT(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkREAL4_EMPTY(const ast::REAL4_EMPTY * ast ,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2,std::shared_ptr<float> value3) {


    coords::REAL4_EMPTY* coords = ast2coords_->mkREAL4_EMPTY(ast, context_ ,value0,value1,value2,value3);

    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({});
    coords2dom_->putREAL4_EMPTY(coords, dom);


    interp::REAL4_EMPTY* interp = new interp::REAL4_EMPTY(coords, dom);
    coords2interp_->putREAL4_EMPTY(coords, interp);
    interp2domain_->putREAL4_EMPTY(interp, dom); 
	this->REAL4_LITERAL_vec.push_back(coords);

} 


 std::string Interpretation::toString_REAL4_LITERALs(){ 
    std::vector<interp::REAL4_LITERAL*> interps;
    for(auto coord : this->REAL4_LITERAL_vec){
        interps.push_back(this->coords2interp_->getREAL4_LITERAL(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(const ast::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2,ast::REAL1_EXPR* operand3,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) {

	coords::REAL1_EXPR* operand1_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL1_EXPR* operand2_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand2));;
	coords::REAL1_EXPR* operand3_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand3));

    coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* coords = ast2coords_->mkREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(ast, context_ ,operand1_coords,operand2_coords,operand3_coords,value0,value1,value2);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL1_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL1_EXPR(operand2_coords);
	domain::DomainObject* operand3_dom = coords2dom_->getREAL1_EXPR(operand3_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom,operand3_dom});
    coords2dom_->putREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords, dom);

	interp::REAL1_EXPR* operand1_interp = coords2interp_->getREAL1_EXPR(operand1_coords);;
	interp::REAL1_EXPR* operand2_interp = coords2interp_->getREAL1_EXPR(operand2_coords);;
	interp::REAL1_EXPR* operand3_interp = coords2interp_->getREAL1_EXPR(operand3_coords);

    interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* interp = new interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords, dom, operand1_interp,operand2_interp,operand3_interp);
    coords2interp_->putREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords, interp);
    interp2domain_->putREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp, dom); 
	this->REAL3_LITERAL_vec.push_back(coords);

} 

void Interpretation::mkREAL3_EMPTY(const ast::REAL3_EMPTY * ast ,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) {


    coords::REAL3_EMPTY* coords = ast2coords_->mkREAL3_EMPTY(ast, context_ ,value0,value1,value2);

    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({});
    coords2dom_->putREAL3_EMPTY(coords, dom);


    interp::REAL3_EMPTY* interp = new interp::REAL3_EMPTY(coords, dom);
    coords2interp_->putREAL3_EMPTY(coords, interp);
    interp2domain_->putREAL3_EMPTY(interp, dom); 
	this->REAL3_LITERAL_vec.push_back(coords);

} 


 std::string Interpretation::toString_REAL3_LITERALs(){ 
    std::vector<interp::REAL3_LITERAL*> interps;
    for(auto coord : this->REAL3_LITERAL_vec){
        interps.push_back(this->coords2interp_->getREAL3_LITERAL(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkREAL1_LIT(const ast::REAL1_LIT * ast ,std::shared_ptr<float> value0) {


    coords::REAL1_LIT* coords = ast2coords_->mkREAL1_LIT(ast, context_ ,value0);

    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({});
    coords2dom_->putREAL1_LIT(coords, dom);


    interp::REAL1_LIT* interp = new interp::REAL1_LIT(coords, dom);
    coords2interp_->putREAL1_LIT(coords, interp);
    interp2domain_->putREAL1_LIT(interp, dom); 
	this->REAL1_LITERAL_vec.push_back(coords);

} 


 std::string Interpretation::toString_REAL1_LITERALs(){ 
    std::vector<interp::REAL1_LITERAL*> interps;
    for(auto coord : this->REAL1_LITERAL_vec){
        interps.push_back(this->coords2interp_->getREAL1_LITERAL(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkREALMATRIX4_EMPTY(const ast::REALMATRIX4_EMPTY * ast ) {


    coords::REALMATRIX4_EMPTY* coords = ast2coords_->mkREALMATRIX4_EMPTY(ast, context_ );

    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({});
    coords2dom_->putREALMATRIX4_EMPTY(coords, dom);


    interp::REALMATRIX4_EMPTY* interp = new interp::REALMATRIX4_EMPTY(coords, dom);
    coords2interp_->putREALMATRIX4_EMPTY(coords, interp);
    interp2domain_->putREALMATRIX4_EMPTY(interp, dom); 
	this->REALMATRIX4_LITERAL_vec.push_back(coords);

} 

void Interpretation::mkREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(const ast::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR * ast ,ast::REALMATRIX4_EXPR* operand1) {

	coords::REALMATRIX4_EXPR* operand1_coords = static_cast<coords::REALMATRIX4_EXPR*>(ast2coords_->getStmtCoords(operand1));

    coords::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR* coords = ast2coords_->mkREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREALMATRIX4_EXPR(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(coords, dom);

	interp::REALMATRIX4_EXPR* operand1_interp = coords2interp_->getREALMATRIX4_EXPR(operand1_coords);

    interp::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR* interp = new interp::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR(coords, dom, operand1_interp);
    coords2interp_->putREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(coords, interp);
    interp2domain_->putREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(interp, dom); 
	this->REALMATRIX4_LITERAL_vec.push_back(coords);

} 

void Interpretation::mkR4R3_LIT_REAL4_EXPR_REAL3_EXPR(const ast::R4R3_LIT_REAL4_EXPR_REAL3_EXPR * ast ,ast::REAL4_EXPR* operand1,ast::REAL3_EXPR* operand2) {

	coords::REAL4_EXPR* operand1_coords = static_cast<coords::REAL4_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL3_EXPR* operand2_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::R4R3_LIT_REAL4_EXPR_REAL3_EXPR* coords = ast2coords_->mkR4R3_LIT_REAL4_EXPR_REAL3_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL4_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL3_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putR4R3_LIT_REAL4_EXPR_REAL3_EXPR(coords, dom);

	interp::REAL4_EXPR* operand1_interp = coords2interp_->getREAL4_EXPR(operand1_coords);;
	interp::REAL3_EXPR* operand2_interp = coords2interp_->getREAL3_EXPR(operand2_coords);

    interp::R4R3_LIT_REAL4_EXPR_REAL3_EXPR* interp = new interp::R4R3_LIT_REAL4_EXPR_REAL3_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putR4R3_LIT_REAL4_EXPR_REAL3_EXPR(coords, interp);
    interp2domain_->putR4R3_LIT_REAL4_EXPR_REAL3_EXPR(interp, dom); 
	this->REALMATRIX4_LITERAL_vec.push_back(coords);

} 


 std::string Interpretation::toString_REALMATRIX4_LITERALs(){ 
    std::vector<interp::REALMATRIX4_LITERAL*> interps;
    for(auto coord : this->REALMATRIX4_LITERAL_vec){
        interps.push_back(this->coords2interp_->getREALMATRIX4_LITERAL(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkIGNORE(const ast::IGNORE * ast ) {


    coords::IGNORE* coords = ast2coords_->mkIGNORE(ast, context_ );

    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({});
    coords2dom_->putIGNORE(coords, dom);


    interp::IGNORE* interp = new interp::IGNORE(coords, dom);
    coords2interp_->putIGNORE(coords, interp);
    interp2domain_->putIGNORE(interp, dom); 
	this->SINK_vec.push_back(coords);

} 


 std::string Interpretation::toString_SINKs(){ 
    std::vector<interp::SINK*> interps;
    for(auto coord : this->SINK_vec){
        interps.push_back(this->coords2interp_->getSINK(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkBOOL_LIT(const ast::BOOL_LIT * ast ,std::shared_ptr<bool> value0) {


    coords::BOOL_LIT* coords = ast2coords_->mkBOOL_LIT(ast, context_ ,value0);

    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({});
    coords2dom_->putBOOL_LIT(coords, dom);


    interp::BOOL_LIT* interp = new interp::BOOL_LIT(coords, dom);
    coords2interp_->putBOOL_LIT(coords, interp);
    interp2domain_->putBOOL_LIT(interp, dom); 
	this->BOOL_LITERAL_vec.push_back(coords);

} 


 std::string Interpretation::toString_BOOL_LITERALs(){ 
    std::vector<interp::BOOL_LITERAL*> interps;
    for(auto coord : this->BOOL_LITERAL_vec){
        interps.push_back(this->coords2interp_->getBOOL_LITERAL(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}


std::string Interpretation::toString_Spaces() {
      //  int index = 0;
    std::string retval = "";
    //std::vector<domain::Space*> & s = domain_->getSpaces();
    //for (std::vector<domain::Space*>::iterator it = s.begin(); it != s.end(); ++it)
     //   retval = retval.append("def ")
     //                   .append((*it)->toString())
     //                   .append(" : peirce.vector_space := peirce.vector_space.mk ")
     //                   .append(std::to_string(index++))
     //                   .append("\n");
     //auto spaces = domain_->getSpaces();
    
	auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
    for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        retval.append("\n" + (sp->toString()) + "\n");
    }
            
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
    for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        retval.append("\n" + (sp->toString()) + "\n");
    }
            
	auto EuclideanGeometry3s = domain_->getEuclideanGeometry3Spaces();
    for (auto it = EuclideanGeometry3s.begin(); it != EuclideanGeometry3s.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        retval.append("\n" + (sp->toString()) + "\n");
    }
            
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        retval.append("\n" + (sp->toString()) + "\n");
    }
            
	auto ClassicalHertzs = domain_->getClassicalHertzSpaces();
    for (auto it = ClassicalHertzs.begin(); it != ClassicalHertzs.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        retval.append("\n" + (sp->toString()) + "\n");
    }
            

    return retval;
}   

std::vector<interp::Space*> Interpretation::getSpaceInterps() {
    std::vector<interp::Space*> interps;
    
	auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
    for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        interps.push_back(sp);
    }
            
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
    for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        interps.push_back(sp);
    }
            
	auto EuclideanGeometry3s = domain_->getEuclideanGeometry3Spaces();
    for (auto it = EuclideanGeometry3s.begin(); it != EuclideanGeometry3s.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        interps.push_back(sp);
    }
            
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        interps.push_back(sp);
    }
            
	auto ClassicalHertzs = domain_->getClassicalHertzSpaces();
    for (auto it = ClassicalHertzs.begin(); it != ClassicalHertzs.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        interps.push_back(sp);
    }
            

    return interps;
}   

std::vector<interp::MeasurementSystem*> Interpretation::getMSInterps(){
    std::vector<interp::MeasurementSystem*> interps;
    auto mss = domain_->getMeasurementSystems();
    for (auto& m : mss)
    {
        auto ms = interp2domain_->getMeasurementSystem(m);
        interps.push_back(ms);
    }
    return interps;
};

std::vector<interp::AxisOrientation*> Interpretation::getAxisInterps(){
    std::vector<interp::AxisOrientation*> interps;
    auto mss = domain_->getAxisOrientations();
    for (auto& m : mss)
    {
        auto ms = interp2domain_->getAxisOrientation(m);
        interps.push_back(ms);
    }
    return interps;
};

std::vector<std::string> Interpretation::getSpaceNames() {
    std::vector<std::string> names;
    
	auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
    for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
    {
        //auto sp = interp2domain_->getSpace(*it);
        names.push_back((*it)->getName());
    }
            
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
    for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
    {
        //auto sp = interp2domain_->getSpace(*it);
        names.push_back((*it)->getName());
    }
            
	auto EuclideanGeometry3s = domain_->getEuclideanGeometry3Spaces();
    for (auto it = EuclideanGeometry3s.begin(); it != EuclideanGeometry3s.end(); it++)
    {
        //auto sp = interp2domain_->getSpace(*it);
        names.push_back((*it)->getName());
    }
            
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
    {
        //auto sp = interp2domain_->getSpace(*it);
        names.push_back((*it)->getName());
    }
            
	auto ClassicalHertzs = domain_->getClassicalHertzSpaces();
    for (auto it = ClassicalHertzs.begin(); it != ClassicalHertzs.end(); it++)
    {
        //auto sp = interp2domain_->getSpace(*it);
        names.push_back((*it)->getName());
    }
            

    return names;
}

std::vector<std::string> Interpretation::getMSNames(){
    std::vector<std::string> names;
    auto mss = domain_->getMeasurementSystems();
    for (auto& m : mss)
    {
        names.push_back(m->getName());
    }
    return names;
};

std::vector<std::string> Interpretation::getAxisNames(){
    std::vector<std::string> names;
    auto axs = domain_->getAxisOrientations();
    for (auto& ax : axs)
    {
        names.push_back(ax->getName());
    }
    return names;
};


std::vector<interp::Frame*> Interpretation::getFrameInterps() {
    std::vector<interp::Frame*> interps;
    
	auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
    for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            /*if(auto dc = dynamic_cast<domain::EuclideanGeometryAliasedFrame*>(fr)){
                auto intfr = interp2domain_->getFrame(fr);
                interps.push_back(intfr);
            }*/
            if(auto dc = dynamic_cast<domain::EuclideanGeometryStandardFrame*>(fr)){
                
            }
            else{
                auto intfr = interp2domain_->getFrame(fr);
                interps.push_back(intfr);
                
            }
            
        }
    }
            
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
    for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            /*if(auto dc = dynamic_cast<domain::ClassicalTimeAliasedFrame*>(fr)){
                auto intfr = interp2domain_->getFrame(fr);
                interps.push_back(intfr);
            }*/
            if(auto dc = dynamic_cast<domain::ClassicalTimeStandardFrame*>(fr)){
                
            }
            else{
                auto intfr = interp2domain_->getFrame(fr);
                interps.push_back(intfr);
                
            }
            
        }
    }
            
	auto EuclideanGeometry3s = domain_->getEuclideanGeometry3Spaces();
    for (auto it = EuclideanGeometry3s.begin(); it != EuclideanGeometry3s.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            /*if(auto dc = dynamic_cast<domain::EuclideanGeometry3AliasedFrame*>(fr)){
                auto intfr = interp2domain_->getFrame(fr);
                interps.push_back(intfr);
            }*/
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3StandardFrame*>(fr)){
                
            }
            else{
                auto intfr = interp2domain_->getFrame(fr);
                interps.push_back(intfr);
                
            }
            
        }
    }
            
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            /*if(auto dc = dynamic_cast<domain::ClassicalVelocityAliasedFrame*>(fr)){
                auto intfr = interp2domain_->getFrame(fr);
                interps.push_back(intfr);
            }*/
            if(auto dc = dynamic_cast<domain::ClassicalVelocityStandardFrame*>(fr)){
                
            }
            else{
                auto intfr = interp2domain_->getFrame(fr);
                interps.push_back(intfr);
                
            }
            
        }
    }
            
	auto ClassicalHertzs = domain_->getClassicalHertzSpaces();
    for (auto it = ClassicalHertzs.begin(); it != ClassicalHertzs.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            /*if(auto dc = dynamic_cast<domain::ClassicalHertzAliasedFrame*>(fr)){
                auto intfr = interp2domain_->getFrame(fr);
                interps.push_back(intfr);
            }*/
            if(auto dc = dynamic_cast<domain::ClassicalHertzStandardFrame*>(fr)){
                
            }
            else{
                auto intfr = interp2domain_->getFrame(fr);
                interps.push_back(intfr);
                
            }
            
        }
    }
            

    return interps;
}   

std::vector<std::string> Interpretation::getFrameNames() {
    std::vector<std::string> names;
    
	auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
    for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            //if(auto dc = dynamic_cast<domain::EuclideanGeometryAliasedFrame*>(fr)){
            //if(!(domain::StandardFrame*)fr){
                names.push_back((*it)->getName()+"."+fr->getName());
            //}
            //}
            
            if(auto dc = dynamic_cast<domain::EuclideanGeometryStandardFrame*>(fr)){
                
            }
            else{
                names.push_back((*it)->getName()+"."+fr->getName());
            }
        }
    }
            
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
    for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            //if(auto dc = dynamic_cast<domain::ClassicalTimeAliasedFrame*>(fr)){
            //if(!(domain::StandardFrame*)fr){
                names.push_back((*it)->getName()+"."+fr->getName());
            //}
            //}
            
            if(auto dc = dynamic_cast<domain::ClassicalTimeStandardFrame*>(fr)){
                
            }
            else{
                names.push_back((*it)->getName()+"."+fr->getName());
            }
        }
    }
            
	auto EuclideanGeometry3s = domain_->getEuclideanGeometry3Spaces();
    for (auto it = EuclideanGeometry3s.begin(); it != EuclideanGeometry3s.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            //if(auto dc = dynamic_cast<domain::EuclideanGeometry3AliasedFrame*>(fr)){
            //if(!(domain::StandardFrame*)fr){
                names.push_back((*it)->getName()+"."+fr->getName());
            //}
            //}
            
            if(auto dc = dynamic_cast<domain::EuclideanGeometry3StandardFrame*>(fr)){
                
            }
            else{
                names.push_back((*it)->getName()+"."+fr->getName());
            }
        }
    }
            
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            //if(auto dc = dynamic_cast<domain::ClassicalVelocityAliasedFrame*>(fr)){
            //if(!(domain::StandardFrame*)fr){
                names.push_back((*it)->getName()+"."+fr->getName());
            //}
            //}
            
            if(auto dc = dynamic_cast<domain::ClassicalVelocityStandardFrame*>(fr)){
                
            }
            else{
                names.push_back((*it)->getName()+"."+fr->getName());
            }
        }
    }
            
	auto ClassicalHertzs = domain_->getClassicalHertzSpaces();
    for (auto it = ClassicalHertzs.begin(); it != ClassicalHertzs.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            //if(auto dc = dynamic_cast<domain::ClassicalHertzAliasedFrame*>(fr)){
            //if(!(domain::StandardFrame*)fr){
                names.push_back((*it)->getName()+"."+fr->getName());
            //}
            //}
            
            if(auto dc = dynamic_cast<domain::ClassicalHertzStandardFrame*>(fr)){
                
            }
            else{
                names.push_back((*it)->getName()+"."+fr->getName());
            }
        }
    }
            

    return names;
}




    
void Interpretation::buildDefaultSpaces(){
    


}

void Interpretation::buildSpace(){
    int index = 0;
    int choice = 0;
    int size = 5;
    if (size == 0){
        std::cout<<"Warning: No Available Spaces to Build";
        return;
    }
    while((choice <= 0 or choice > size)){ 
        std::cout<<"Available types of Spaces to build:\n";
        std::cout <<"("<<std::to_string(++index)<<")"<<"EuclideanGeometry\n";
		std::cout <<"("<<std::to_string(++index)<<")"<<"ClassicalTime\n";
		std::cout <<"("<<std::to_string(++index)<<")"<<"EuclideanGeometry3\n";
		std::cout <<"("<<std::to_string(++index)<<")"<<"ClassicalVelocity\n";
		std::cout <<"("<<std::to_string(++index)<<")"<<"ClassicalHertz\n";
        std::cin>>choice;
        choice_buffer->push_back(std::to_string(choice));
    }
    index = 0;
    
        if(choice==++index){
            std::string name;
            std::cout<<"Enter Name (string):\n";
            std::cin>>name;
        choice_buffer->push_back(name);
            
            int dimension;
            std::cout<<"Enter Dimension (integer):\n";
            std::cin>>dimension;
        choice_buffer->push_back(std::to_string(dimension));
            auto sp = this->domain_->mkEuclideanGeometry(name, name, dimension);
    
            auto isp = new interp::Space(sp);
            interp2domain_->putSpace(isp, sp);
            auto standard_framesp = sp->getFrames()[0];
            auto interp_framesp = new interp::Frame(standard_framesp, isp);
            interp2domain_->putFrame(interp_framesp, sp->getFrames()[0]);
        }

    
	
        if(choice==++index){
            std::string name;
            std::cout<<"Enter Name (string):\n";
            std::cin>>name;
        choice_buffer->push_back(name);
            
            auto sp = this->domain_->mkClassicalTime(name, name);
            auto isp = new interp::Space(sp);
            interp2domain_->putSpace(isp, sp);
            auto standard_framesp = sp->getFrames()[0];
            auto interp_framesp = new interp::Frame(standard_framesp, isp);
            interp2domain_->putFrame(interp_framesp, sp->getFrames()[0]);
        }

    
	
        if(choice==++index){
            std::string name;
            std::cout<<"Enter Name (string):\n";
            std::cin>>name;
        choice_buffer->push_back(name);
            
            auto sp = this->domain_->mkEuclideanGeometry3(name, name);
            auto isp = new interp::Space(sp);
            interp2domain_->putSpace(isp, sp);
            auto standard_framesp = sp->getFrames()[0];
            auto interp_framesp = new interp::Frame(standard_framesp, isp);
            interp2domain_->putFrame(interp_framesp, sp->getFrames()[0]);
        }

    
	
        if(choice==++index){
            std::string name;
            domain::Space *base1,*base2;
            std::cout<<"Enter Name (string):\n";
            std::cin>>name;
        choice_buffer->push_back(name);
            int index = 0;
            std::unordered_map<int, domain::Space*> index_to_sp;
        
	auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
            for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
            {
                std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
                index_to_sp[index] = *it;
            }
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
            for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
            {
                std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
                index_to_sp[index] = *it;
            }
	auto EuclideanGeometry3s = domain_->getEuclideanGeometry3Spaces();
            for (auto it = EuclideanGeometry3s.begin(); it != EuclideanGeometry3s.end(); it++)
            {
                std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
                index_to_sp[index] = *it;
            }
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
            for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
            {
                std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
                index_to_sp[index] = *it;
            }
	auto ClassicalHertzs = domain_->getClassicalHertzSpaces();
            for (auto it = ClassicalHertzs.begin(); it != ClassicalHertzs.end(); it++)
            {
                std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
                index_to_sp[index] = *it;
            }

            if(index==0){
                std::cout<<"Unable to Proceed - No Existing Spaces\n";
                return;
            }
            int choice;
            ClassicalVelocitylabel1st:
            std::cout<<"Select First Base Space : "<<"\n";
            std::cin>>choice;
        choice_buffer->push_back(std::to_string(choice));
            if(choice >0 and choice <=index){
                base1 = index_to_sp[choice];
            }
            else
                goto ClassicalVelocitylabel1st;
            
            ClassicalVelocitylabel2nd:
            std::cout<<"Select Second Base Space : "<<"\n";
            std::cin>>choice;
        choice_buffer->push_back(std::to_string(choice));
            if(choice >0 and choice <=index){
                base2 = index_to_sp[choice];
            }
            else
                goto ClassicalVelocitylabel2nd;
            auto sp = this->domain_->mkClassicalVelocity(name, name, base1, base2);
            auto ib1 = this->interp2domain_->getSpace(base1);
            auto ib2 = this->interp2domain_->getSpace(base2);

            auto isp = new interp::DerivedSpace(sp, ib1, ib2);
            interp2domain_->putSpace(isp, sp);
            auto standard_framesp = sp->getFrames()[0];
            auto interp_framesp = new interp::Frame(standard_framesp, isp);
            interp2domain_->putFrame(interp_framesp, sp->getFrames()[0]);
        }

	
        if(choice==++index){
            std::string name;
            std::cout<<"Enter Name (string):\n";
            std::cin>>name;
        choice_buffer->push_back(name);
            
            auto sp = this->domain_->mkClassicalHertz(name, name);
            auto isp = new interp::Space(sp);
            interp2domain_->putSpace(isp, sp);
            auto standard_framesp = sp->getFrames()[0];
            auto interp_framesp = new interp::Frame(standard_framesp, isp);
            interp2domain_->putFrame(interp_framesp, sp->getFrames()[0]);
        }

    
}

void Interpretation::buildMeasurementSystem(){
    while(true){
        std::cout<<"Build Measurement System : \n";
        std::cout<<"(1) SI Measurement System \n";
        std::cout<<"(2) Imperial Measurement System\n";
        int choice = 0;
        std::cin>>choice;
        choice_buffer->push_back(std::to_string(choice));
        if(choice == 1){
            std::cout<<"Enter reference name:";
            std::string nm;
            std::cin>>nm;
        choice_buffer->push_back(nm);
            auto ms = this->domain_->mkSIMeasurementSystem(nm);
            auto ims = new interp::MeasurementSystem(ms);
            interp2domain_->putMeasurementSystem(ims, ms);
            return;
        }
        else if (choice == 2){
            std::cout<<"Enter reference name:";
            std::string nm;
            std::cin>>nm;
        choice_buffer->push_back(nm);
            auto ms = this->domain_->mkImperialMeasurementSystem(nm);
            auto ims = new interp::MeasurementSystem(ms);
            interp2domain_->putMeasurementSystem(ims, ms);
            return;
        }
    }

};

void Interpretation::printMeasurementSystems(){
    auto ms = this->domain_->getMeasurementSystems();
    for(auto& m:ms){
        std::cout<<m->toString()<<"\n";
    }

};



void Interpretation::buildAxisOrientation(){
    while(true){
        std::cout<<"Build Axis Orientation : \n";
        std::cout<<"(1) NWU Orientation (Standard body - X north, Y west, Z up) \n";
        std::cout<<"(2) NED Orientation\n";
        std::cout<<"(3) ENU Orientation\n";
        int choice = 0;
        std::cin>>choice;
        choice_buffer->push_back(std::to_string(choice));
        if(choice == 1){
            std::cout<<"Enter reference name:";
            std::string nm;
            std::cin>>nm;
            choice_buffer->push_back(nm);
            auto ax = this->domain_->mkNWUOrientation(nm);
            auto iax = new interp::AxisOrientation(ax);
            interp2domain_->putAxisOrientation(iax, ax);
            return;
        }
        else if (choice == 2){
            std::cout<<"Enter reference name:";
            std::string nm;
            std::cin>>nm;
            choice_buffer->push_back(nm);
            auto ax = this->domain_->mkNEDOrientation(nm);
            auto iax = new interp::AxisOrientation(ax);
            interp2domain_->putAxisOrientation(iax, ax);
            return;
        }
        else if (choice == 3){
            std::cout<<"Enter reference name:";
            std::string nm;
            std::cin>>nm;
            choice_buffer->push_back(nm);
            auto ax = this->domain_->mkENUOrientation(nm);
            auto iax = new interp::AxisOrientation(ax);
            interp2domain_->putAxisOrientation(iax, ax);
            return;
        }
    }

};

void Interpretation::printAxisOrientations(){
    auto axs = this->domain_->getAxisOrientations();
    for(auto& ax:axs){
        std::cout<<ax->toString()<<"\n";
    }

};


//1/18/20 : Probably worth revisiting this method and input in general in the feature
void Interpretation::buildFrame(){
    while(true){
        std::cout<<"Select Space : "<<"\n";
        int index = 0;
        std::unordered_map<int, domain::Space*> index_to_sp;
    
		auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
        for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
        {
            std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
            index_to_sp[index] = *it;
        }
		auto ClassicalTimes = domain_->getClassicalTimeSpaces();
        for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
        {
            std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
            index_to_sp[index] = *it;
        }
		auto EuclideanGeometry3s = domain_->getEuclideanGeometry3Spaces();
        for (auto it = EuclideanGeometry3s.begin(); it != EuclideanGeometry3s.end(); it++)
        {
            std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
            index_to_sp[index] = *it;
        }
		auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
        for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
        {
            std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
            index_to_sp[index] = *it;
        }
		auto ClassicalHertzs = domain_->getClassicalHertzSpaces();
        for (auto it = ClassicalHertzs.begin(); it != ClassicalHertzs.end(); it++)
        {
            std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
            index_to_sp[index] = *it;
        }
        int choice;
        std::cin>>choice;
        choice_buffer->push_back(std::to_string(choice));
        if(choice >0 and choice <=index){
            auto chosen = index_to_sp[choice];
            std::cout<<"Building Frame For : "<<chosen->toString()<<"\n";
            int frameType = 0;

            while(true){
                std::cout<<"Select Frame Type : \n";
                std::cout<<" (1) Alias For Existing Frame \n";
                std::cout<<" (2) Derived Frame From Existing Frame \n";
                std::cin>>frameType;
                choice_buffer->push_back(std::to_string(frameType));

                if(frameType == 1){
                    auto frames = chosen->getFrames();
                    std::cout<<"Select Frame To Alias : "<<"\n";
                    index = 0;
                    std::unordered_map<int, domain::Frame*> index_to_fr;
        
                    auto frs = chosen->getFrames();
                    for(auto fr : frs){
                    std::cout<<"("<<std::to_string(++index)<<")"<<(fr)->toString()<<"\n";
                    index_to_fr[index] = fr;
                    }
                    choice = 0;
                    std::cin>>choice;
                    choice_buffer->push_back(std::to_string(choice));

                    if(choice > 0 and choice<= index){
                        auto aliased = index_to_fr[choice];
                        std::cout<<"Enter Name:\n";
                        std::string name;
                        std::cin>>name;
                        choice_buffer->push_back(name);
                        //domain::MeasurementSystem* ms;
                        auto mss = this->domain_->getMeasurementSystems();
                        std::unordered_map<int, domain::MeasurementSystem*> index_to_ms;

                        ms:

                        index_to_ms.clear();
                        choice = 0;
                        index = 0;
                        std::cout<<"Select Measurement System to Interpret Frame With : \n";
                        for(auto& m : mss){
                            std::cout<<"("<<std::to_string(++index)<<")"<<(m)->toString()<<"\n";
                            index_to_ms[index] = m;
                        }
                        if(index == 0){
                            std::cout<<"Warning: No available Measurement Systems! You must instantiate one in order to provide an intepretation to the frame.";
                            return;
                        }
                        std::cin>>choice;
                        choice_buffer->push_back(std::to_string(choice));
                        

                        if(choice<0 or choice>index){
                            goto ms;
                        }
                        
                        auto cms = index_to_ms[choice];

                        auto axs = this->domain_->getAxisOrientations();
                        std::unordered_map<int, domain::AxisOrientation*> index_to_ax;

                        ax:

                        choice = 0;
                        index = 0;
                        std::cout<<"Select Axis Orientation to Interpret Frame With : \n";
                        for(auto& ax : axs){
                            std::cout<<"("<<std::to_string(++index)<<")"<<(ax)->toString()<<"\n";
                            index_to_ax[index] = ax;
                        }
                        if(index == 0){
                            std::cout<<"Warning: No available Axis Orientations! You must instantiate one in order to provide an intepretation to the frame.";
                            return;
                        }
                        std::cin>>choice;
                        choice_buffer->push_back(std::to_string(choice));

                        if(choice<0 or choice>index){
                            goto ax;
                        }

                        auto cax = index_to_ax[choice];

                        if(choice>0 and choice<=index){


                        if(auto dc = dynamic_cast<domain::EuclideanGeometry*>(chosen)){

                            auto child = (domain::EuclideanGeometryFrame*)domain_->mkEuclideanGeometryAliasedFrame(name, dc, (domain::EuclideanGeometryFrame*)aliased,cms,cax);
                            auto isp = interp2domain_->getSpace(dc);
                            auto ims = interp2domain_->getMeasurementSystem(cms);
                            auto iax = interp2domain_->getAxisOrientation(cax);
                            interp::Frame* interp = new interp::Frame(child, isp, ims, iax);
                            interp2domain_->putFrame(interp, child);
                            return;
                        }
                        if(auto dc = dynamic_cast<domain::ClassicalTime*>(chosen)){

                            auto child = (domain::ClassicalTimeFrame*)domain_->mkClassicalTimeAliasedFrame(name, dc, (domain::ClassicalTimeFrame*)aliased,cms,cax);
                            auto isp = interp2domain_->getSpace(dc);
                            auto ims = interp2domain_->getMeasurementSystem(cms);
                            auto iax = interp2domain_->getAxisOrientation(cax);
                            interp::Frame* interp = new interp::Frame(child, isp, ims, iax);
                            interp2domain_->putFrame(interp, child);
                            return;
                        }
                        if(auto dc = dynamic_cast<domain::EuclideanGeometry3*>(chosen)){

                            auto child = (domain::EuclideanGeometry3Frame*)domain_->mkEuclideanGeometry3AliasedFrame(name, dc, (domain::EuclideanGeometry3Frame*)aliased,cms,cax);
                            auto isp = interp2domain_->getSpace(dc);
                            auto ims = interp2domain_->getMeasurementSystem(cms);
                            auto iax = interp2domain_->getAxisOrientation(cax);
                            interp::Frame* interp = new interp::Frame(child, isp, ims, iax);
                            interp2domain_->putFrame(interp, child);
                            return;
                        }
                        if(auto dc = dynamic_cast<domain::ClassicalVelocity*>(chosen)){

                            auto child = (domain::ClassicalVelocityFrame*)domain_->mkClassicalVelocityAliasedFrame(name, dc, (domain::ClassicalVelocityFrame*)aliased,cms,cax);
                            auto isp = interp2domain_->getSpace(dc);
                            auto ims = interp2domain_->getMeasurementSystem(cms);
                            auto iax = interp2domain_->getAxisOrientation(cax);
                            interp::Frame* interp = new interp::Frame(child, isp, ims, iax);
                            interp2domain_->putFrame(interp, child);
                            return;
                        }
                        if(auto dc = dynamic_cast<domain::ClassicalHertz*>(chosen)){

                            auto child = (domain::ClassicalHertzFrame*)domain_->mkClassicalHertzAliasedFrame(name, dc, (domain::ClassicalHertzFrame*)aliased,cms,cax);
                            auto isp = interp2domain_->getSpace(dc);
                            auto ims = interp2domain_->getMeasurementSystem(cms);
                            auto iax = interp2domain_->getAxisOrientation(cax);
                            interp::Frame* interp = new interp::Frame(child, isp, ims, iax);
                            interp2domain_->putFrame(interp, child);
                            return;
                        }
                    }
                    }
                }
                else if (frameType == 2){
                    auto frames = chosen->getFrames();
                    std::cout<<"Select Parent Frame : "<<"\n";
                    index = 0;
                    std::unordered_map<int, domain::Frame*> index_to_fr;
        
                    auto frs = chosen->getFrames();
                    for(auto fr : frs){
                    std::cout<<"("<<std::to_string(++index)<<")"<<(fr)->toString()<<"\n";
                    index_to_fr[index] = fr;
                    }
                    choice = 0;
                    std::cin>>choice;
                    choice_buffer->push_back(std::to_string(choice));
                    if(choice > 0 and choice<= index){
                        auto parent = index_to_fr[choice];
                        std::cout<<"Enter Name of Frame:\n";
                        std::string name;
                        std::cin>>name;
                        choice_buffer->push_back(name);

                        auto der = dynamic_cast<domain::DerivedFrame*>(parent);
                        auto al = dynamic_cast<domain::AliasedFrame*>(parent);
                        bool reinterpret=false;

                        if
                            (
                            (der && der->getUnits() && der->getOrientation()) ||
                            (al && al->getUnits() && al->getOrientation())
                            )
                        {
                            std::cout<<"Use available measurement units & orientation from Parent Frame? (1 - Yes, 2 - No)\n";
                            std::cin>>choice;
                            choice_buffer->push_back(std::to_string(choice));
                            if(choice == 2)
                                reinterpret = true;
                        }
                        else
                            reinterpret = true;

                        domain::MeasurementSystem* cms;                       
                        domain::AxisOrientation* cax;

                        if(reinterpret){
                            ms2:
                            auto mss = this->domain_->getMeasurementSystems();
                            std::unordered_map<int, domain::MeasurementSystem*> index_to_ms;

                            index_to_ms.clear();
                            choice = 0;
                            index = 0;
                            std::cout<<"Select Measurement System to Interpret Frame With : \n";
                            for(auto& m : mss){
                                std::cout<<"("<<std::to_string(++index)<<")"<<(m)->toString()<<"\n";
                                index_to_ms[index] = m;
                            }
                            if(index == 0){
                                std::cout<<"Warning: No available Measurement Systems! You must instantiate one in order to provide an intepretation to the frame.";
                                return;
                            }
                            std::cin>>choice;
                            choice_buffer->push_back(std::to_string(choice));
                        

                            if(choice<0 or choice>index){
                                goto ms2;
                            }
                        
                            cms = index_to_ms[choice];

                            auto axs = this->domain_->getAxisOrientations();
                            std::unordered_map<int, domain::AxisOrientation*> index_to_ax;

                            ax2:

                            choice = 0;
                            index = 0;
                            std::cout<<"Select Axis Orientation to Interpret Frame With : \n";
                            for(auto& ax : axs){
                                std::cout<<"("<<std::to_string(++index)<<")"<<(ax)->toString()<<"\n";
                                index_to_ax[index] = ax;
                            }
                            if(index == 0){
                                std::cout<<"Warning: No available Axis Orientations! You must instantiate one in order to provide an intepretation to the frame.";
                                return;
                            }
                            std::cin>>choice;
                            choice_buffer->push_back(std::to_string(choice));

                            if(choice<0 or choice>index){
                                goto ax2;
                            }

                            cax = index_to_ax[choice];
                        }
                        else if(der){
                            cms = der->getUnits();
                            cax = der->getOrientation();
                        }
                        else if(al){
                            cms = al->getUnits();
                            cax = al->getOrientation();
                        }


                        if(auto dc = dynamic_cast<domain::EuclideanGeometry*>(chosen)){

                            auto child = (domain::EuclideanGeometryFrame*)domain_->mkEuclideanGeometryDerivedFrame(name, dc, (domain::EuclideanGeometryFrame*)parent, cms, cax);
                            auto isp = interp2domain_->getSpace(dc);
                            auto ims = interp2domain_->getMeasurementSystem(cms);
                            auto iax = interp2domain_->getAxisOrientation(cax);
                            interp::Frame* interp = new interp::Frame(child, isp, ims, iax);
                            interp2domain_->putFrame(interp, child);
                            return;
                        }
                        if(auto dc = dynamic_cast<domain::ClassicalTime*>(chosen)){

                            auto child = (domain::ClassicalTimeFrame*)domain_->mkClassicalTimeDerivedFrame(name, dc, (domain::ClassicalTimeFrame*)parent, cms, cax);
                            auto isp = interp2domain_->getSpace(dc);
                            auto ims = interp2domain_->getMeasurementSystem(cms);
                            auto iax = interp2domain_->getAxisOrientation(cax);
                            interp::Frame* interp = new interp::Frame(child, isp, ims, iax);
                            interp2domain_->putFrame(interp, child);
                            return;
                        }
                        if(auto dc = dynamic_cast<domain::EuclideanGeometry3*>(chosen)){

                            auto child = (domain::EuclideanGeometry3Frame*)domain_->mkEuclideanGeometry3DerivedFrame(name, dc, (domain::EuclideanGeometry3Frame*)parent, cms, cax);
                            auto isp = interp2domain_->getSpace(dc);
                            auto ims = interp2domain_->getMeasurementSystem(cms);
                            auto iax = interp2domain_->getAxisOrientation(cax);
                            interp::Frame* interp = new interp::Frame(child, isp, ims, iax);
                            interp2domain_->putFrame(interp, child);
                            return;
                        }
                        if(auto dc = dynamic_cast<domain::ClassicalVelocity*>(chosen)){

                            auto child = (domain::ClassicalVelocityFrame*)domain_->mkClassicalVelocityDerivedFrame(name, dc, (domain::ClassicalVelocityFrame*)parent, cms, cax);
                            auto isp = interp2domain_->getSpace(dc);
                            auto ims = interp2domain_->getMeasurementSystem(cms);
                            auto iax = interp2domain_->getAxisOrientation(cax);
                            interp::Frame* interp = new interp::Frame(child, isp, ims, iax);
                            interp2domain_->putFrame(interp, child);
                            return;
                        }
                        if(auto dc = dynamic_cast<domain::ClassicalHertz*>(chosen)){

                            auto child = (domain::ClassicalHertzFrame*)domain_->mkClassicalHertzDerivedFrame(name, dc, (domain::ClassicalHertzFrame*)parent, cms, cax);
                            auto isp = interp2domain_->getSpace(dc);
                            auto ims = interp2domain_->getMeasurementSystem(cms);
                            auto iax = interp2domain_->getAxisOrientation(cax);
                            interp::Frame* interp = new interp::Frame(child, isp, ims, iax);
                            interp2domain_->putFrame(interp, child);
                            return;
                        }
                    }
                }
            }

        }

    }
}

void Interpretation::printSpaces(){
    int index = 0;
    
	auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
    for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
    {
        std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
    }
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
    for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
    {
        std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
    }
	auto EuclideanGeometry3s = domain_->getEuclideanGeometry3Spaces();
    for (auto it = EuclideanGeometry3s.begin(); it != EuclideanGeometry3s.end(); it++)
    {
        std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
    }
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
    {
        std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
    }
	auto ClassicalHertzs = domain_->getClassicalHertzSpaces();
    for (auto it = ClassicalHertzs.begin(); it != ClassicalHertzs.end(); it++)
    {
        std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
    }
}

void Interpretation::printFrames(){
    int index = 0;
    
	auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
    for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
    {
        std::cout<<"Printing Frames For : " + (*it)->toString() + "\n";
        auto frs = (*it)->getFrames();
        index = 0;
        for(auto fr : frs){
            std::cout<<"("<<std::to_string(++index)<<")"<<fr->toString() + "\n";
        }
    }
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
    for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
    {
        std::cout<<"Printing Frames For : " + (*it)->toString() + "\n";
        auto frs = (*it)->getFrames();
        index = 0;
        for(auto fr : frs){
            std::cout<<"("<<std::to_string(++index)<<")"<<fr->toString() + "\n";
        }
    }
	auto EuclideanGeometry3s = domain_->getEuclideanGeometry3Spaces();
    for (auto it = EuclideanGeometry3s.begin(); it != EuclideanGeometry3s.end(); it++)
    {
        std::cout<<"Printing Frames For : " + (*it)->toString() + "\n";
        auto frs = (*it)->getFrames();
        index = 0;
        for(auto fr : frs){
            std::cout<<"("<<std::to_string(++index)<<")"<<fr->toString() + "\n";
        }
    }
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
    {
        std::cout<<"Printing Frames For : " + (*it)->toString() + "\n";
        auto frs = (*it)->getFrames();
        index = 0;
        for(auto fr : frs){
            std::cout<<"("<<std::to_string(++index)<<")"<<fr->toString() + "\n";
        }
    }
	auto ClassicalHertzs = domain_->getClassicalHertzSpaces();
    for (auto it = ClassicalHertzs.begin(); it != ClassicalHertzs.end(); it++)
    {
        std::cout<<"Printing Frames For : " + (*it)->toString() + "\n";
        auto frs = (*it)->getFrames();
        index = 0;
        for(auto fr : frs){
            std::cout<<"("<<std::to_string(++index)<<")"<<fr->toString() + "\n";
        }
    }

}

void Interpretation::mkVarTable(){
    int idx = 0; 
  

    for(auto it = this->REALMATRIX4_EXPR_vec.begin(); it != this->REALMATRIX4_EXPR_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->REAL4_EXPR_vec.begin(); it != this->REAL4_EXPR_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->REAL3_EXPR_vec.begin(); it != this->REAL3_EXPR_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->REAL3_LEXPR_vec.begin(); it != this->REAL3_LEXPR_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->REAL1_EXPR_vec.begin(); it != this->REAL1_EXPR_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->BOOL_VAR_IDENT_vec.begin(); it != this->BOOL_VAR_IDENT_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->REAL1_VAR_IDENT_vec.begin(); it != this->REAL1_VAR_IDENT_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->REAL3_VAR_IDENT_vec.begin(); it != this->REAL3_VAR_IDENT_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->REAL4_VAR_IDENT_vec.begin(); it != this->REAL4_VAR_IDENT_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->REALMATRIX4_VAR_IDENT_vec.begin(); it != this->REALMATRIX4_VAR_IDENT_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->REAL4_LITERAL_vec.begin(); it != this->REAL4_LITERAL_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->REAL3_LITERAL_vec.begin(); it != this->REAL3_LITERAL_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->REAL1_LITERAL_vec.begin(); it != this->REAL1_LITERAL_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->REALMATRIX4_LITERAL_vec.begin(); it != this->REALMATRIX4_LITERAL_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }


}

//print the indexed variable table for the user
void Interpretation::printVarTable(){ 
    
  int sz = this->index2coords_.size();

  for(int i = 1; i<=sz;i++)
  {
    //coords::Coords* coords = this->index2coords_[i];
    if(false){}

    else if(auto dc = dynamic_cast<coords::REF_REALMATRIX4_VAR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREF_REALMATRIX4_VAR(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: Var Expression : Matrix 4 Variable As R-Value, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: Multiplication Expression : R4 Expression * R4 Expression, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REF_REAL4_VAR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREF_REAL4_VAR(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: Var Expression : R4 Variable As R-Value, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::ADD_REAL4_EXPR_REAL4_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getADD_REAL4_EXPR_REAL4_EXPR(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: Addition Expression : R4 Expression + R4 Expression, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::MUL_REAL4_EXPR_REAL4_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getMUL_REAL4_EXPR_REAL4_EXPR(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: Multiplication Expression : R4 Expression * R4 Expression, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REF_REAL3_VAR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREF_REAL3_VAR(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: Var Expression : R3 Variable As R-Value, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::ADD_REAL3_EXPR_REAL3_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getADD_REAL3_EXPR_REAL3_EXPR(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: Addition Expression : R3 Expression + R3 Expression, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::LMUL_REAL1_EXPR_REAL3_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getLMUL_REAL1_EXPR_REAL3_EXPR(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: Multiplication Expression : R1 Expression * R3 Expression, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::RMUL_REAL3_EXPR_REAL1_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getRMUL_REAL3_EXPR_REAL1_EXPR(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: Multiplication Expression : R1 Expression * R3 Expression, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::TMUL_REALMATRIX4_EXPR_REAL3_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getTMUL_REALMATRIX4_EXPR_REAL3_EXPR(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: Multiplication Expression : R4 Matrix Expression * R3 Expression, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::LREF_REAL3_VAR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getLREF_REAL3_VAR(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: Var Expression : R3 Variable As L-Value, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REF_REAL1_VAR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREF_REAL1_VAR(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: Var Expression : R1 Variable As R-Value, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::ADD_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getADD_REAL1_EXPR_REAL1_EXPR(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: Addition Expression : R1 Expression + R1 Expression, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::MUL_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getMUL_REAL1_EXPR_REAL1_EXPR(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: Multiplication Expression : R1 Expression * R1 Expression, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::BOOL_VAR_IDENT*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getBOOL_VAR_IDENT(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: Boolean Identifier	, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREAL1_VAR_IDENT(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: R1 Variable Identifier, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREAL3_VAR_IDENT(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: R3 Variable Identifier, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREAL4_VAR_IDENT(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: R4 Variable Identifier, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REALMATRIX4_VAR_IDENT*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREALMATRIX4_VAR_IDENT(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: 4x4 Matrix Variable Identifier, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REAL4_EMPTY*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREAL4_EMPTY(dc);
        std::cout<<"Index: "<<i<<", "<<"Description:  Real 4 Literal With Empty Constructor, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: R3 Literal From 3 R1 Expressions, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REAL3_EMPTY*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREAL3_EMPTY(dc);
        std::cout<<"Index: "<<i<<", "<<"Description:  Real 3 Literal With Empty Constructor, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REAL1_LIT*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREAL1_LIT(dc);
        std::cout<<"Index: "<<i<<", "<<"Description:  Real 1 Literal, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REALMATRIX4_EMPTY*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREALMATRIX4_EMPTY(dc);
        std::cout<<"Index: "<<i<<", "<<"Description:  Real 4x4 Matrix With Empty Constructor, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(dc);
        std::cout<<"Index: "<<i<<", "<<"Description:  Real 4x4 Matrix With Empty Constructor, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::R4R3_LIT_REAL4_EXPR_REAL3_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getR4R3_LIT_REAL4_EXPR_REAL3_EXPR(dc);
        std::cout<<"Index: "<<i<<", "<<"Description: A Real 4x4 Matrix instantiated with x E R3 and y E R4, \n\t"<<"Snippet: "<<dc->state_->code_<<", \n\t"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<"\n"<<std::endl;

    }
    
  }

}//make a printable, indexed table of variables that can have their types assigned by a user or oracle


void Interpretation::printChoices(){
    aFile* f = new aFile;
    std::string name = "/peirce/annotations.txt";
    char * name_cstr = new char [name.length()+1];
    strcpy (name_cstr, name.c_str());
    f->name = name_cstr;
    std::cout<<"Generating annotations file ... " << name_cstr << "\n";
    f->file = fopen(f->name, "w");
    for(auto choice: *choice_buffer){
        fputs((choice + "\n").c_str(), f->file);
    }

    fclose(f->file);
    delete f->name;
    delete f;
};

//void Interpretation::printVarTable(){}//print the indexed variable table for the user
//while loop where user can select a variable by index and provide a physical type for that variable
void Interpretation::updateVarTable(){
  auto sz = (int)this->index2coords_.size()+1;
  int choice;
  try{
        checker_->CheckPoll();
        //std::cout << "********************************************\n";
        std::cout << "********************************************\n";
        std::cout << "********************************************\n";
        std::cout << "See type-checking output in /peirce/phys/deps/orig/PeirceOutput.lean\n";
        std::cout << "********************************************\n";
        //std::cout << "********************************************\n";
        std::cout << "********************************************\n";
        std::cout<<"Enter -1 to print Available Spaces\n";
        std::cout<<"Enter -2 to create a New Space\n";
        std::cout<<"Enter -3 to print Available Frames\n";
        std::cout<<"Enter -4 to create a New Frame\n";
        std::cout<<"Enter -5 to print available Measurement Systems\n";
        std::cout<<"Enter -6  to create a Measurement System\n";
        std::cout<<"Enter -7 to print available Axis Orientations\n";
        std::cout<<"Enter -8  to create an Axis Orientation\n";
        std::cout<<"Enter 0 to print the Variable Table again.\n";
        std::cout << "Enter the index of a Variable to update its physical type. Enter " << sz << " to exit and check." << std::endl;
        std::cin >> choice;
        choice_buffer->push_back(std::to_string(choice));
        std::cout << std::to_string(choice) << "\n";

        while (((choice >= -8 and choice <= 0) || this->index2coords_.find(choice) != this->index2coords_.end()) && choice != sz)
        {
            if (choice == -8)
            {
                this->buildAxisOrientation();
            }

            if (choice == -7)
            {
                this->printAxisOrientations();
            }

            if (choice == -6)
            {
                this->buildMeasurementSystem();
            }

            if (choice == -5)
            {
                this->printMeasurementSystems();
            }

            if (choice == -4)
            {
                this->buildFrame();
            }
            else if(choice == -3)
            {
                this->printFrames();
            }
            else if(choice == -2)
            {
                this->buildSpace();
            }
            else if (choice == -1)
            {
                this->printSpaces();
            }
            else if (choice == 0)
            {
                this->printVarTable();
            }
            else
            {
                if(false){}

                else if(auto dc = dynamic_cast<coords::REF_REALMATRIX4_VAR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREF_REALMATRIX4_VAR(dc);
                    //auto interp = this->coords2interp_->getREF_REALMATRIX4_VAR(dc);
                    //this->coords2dom_->eraseREF_REALMATRIX4_VAR(dc, dom);
                    //this->interp2domain_->eraseREF_REALMATRIX4_VAR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREALMATRIX4_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREF_REALMATRIX4_VAR(dc, dom);
                        //this->interp2domain_->eraseREF_REALMATRIX4_VAR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREF_REALMATRIX4_VAR(dc, upd_dom);
                        //this->interp2domain_->putREF_REALMATRIX4_VAR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(dc);
                    //auto interp = this->coords2interp_->getMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(dc);
                    //this->coords2dom_->eraseMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(dc, dom);
                    //this->interp2domain_->eraseMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREALMATRIX4_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(dc, dom);
                        //this->interp2domain_->eraseMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(dc, upd_dom);
                        //this->interp2domain_->putMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REF_REAL4_VAR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREF_REAL4_VAR(dc);
                    //auto interp = this->coords2interp_->getREF_REAL4_VAR(dc);
                    //this->coords2dom_->eraseREF_REAL4_VAR(dc, dom);
                    //this->interp2domain_->eraseREF_REAL4_VAR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL4_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREF_REAL4_VAR(dc, dom);
                        //this->interp2domain_->eraseREF_REAL4_VAR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREF_REAL4_VAR(dc, upd_dom);
                        //this->interp2domain_->putREF_REAL4_VAR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::ADD_REAL4_EXPR_REAL4_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getADD_REAL4_EXPR_REAL4_EXPR(dc);
                    //auto interp = this->coords2interp_->getADD_REAL4_EXPR_REAL4_EXPR(dc);
                    //this->coords2dom_->eraseADD_REAL4_EXPR_REAL4_EXPR(dc, dom);
                    //this->interp2domain_->eraseADD_REAL4_EXPR_REAL4_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL4_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseADD_REAL4_EXPR_REAL4_EXPR(dc, dom);
                        //this->interp2domain_->eraseADD_REAL4_EXPR_REAL4_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putADD_REAL4_EXPR_REAL4_EXPR(dc, upd_dom);
                        //this->interp2domain_->putADD_REAL4_EXPR_REAL4_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::MUL_REAL4_EXPR_REAL4_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getMUL_REAL4_EXPR_REAL4_EXPR(dc);
                    //auto interp = this->coords2interp_->getMUL_REAL4_EXPR_REAL4_EXPR(dc);
                    //this->coords2dom_->eraseMUL_REAL4_EXPR_REAL4_EXPR(dc, dom);
                    //this->interp2domain_->eraseMUL_REAL4_EXPR_REAL4_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL4_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseMUL_REAL4_EXPR_REAL4_EXPR(dc, dom);
                        //this->interp2domain_->eraseMUL_REAL4_EXPR_REAL4_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putMUL_REAL4_EXPR_REAL4_EXPR(dc, upd_dom);
                        //this->interp2domain_->putMUL_REAL4_EXPR_REAL4_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REF_REAL3_VAR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREF_REAL3_VAR(dc);
                    //auto interp = this->coords2interp_->getREF_REAL3_VAR(dc);
                    //this->coords2dom_->eraseREF_REAL3_VAR(dc, dom);
                    //this->interp2domain_->eraseREF_REAL3_VAR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL3_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREF_REAL3_VAR(dc, dom);
                        //this->interp2domain_->eraseREF_REAL3_VAR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREF_REAL3_VAR(dc, upd_dom);
                        //this->interp2domain_->putREF_REAL3_VAR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::ADD_REAL3_EXPR_REAL3_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getADD_REAL3_EXPR_REAL3_EXPR(dc);
                    //auto interp = this->coords2interp_->getADD_REAL3_EXPR_REAL3_EXPR(dc);
                    //this->coords2dom_->eraseADD_REAL3_EXPR_REAL3_EXPR(dc, dom);
                    //this->interp2domain_->eraseADD_REAL3_EXPR_REAL3_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL3_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseADD_REAL3_EXPR_REAL3_EXPR(dc, dom);
                        //this->interp2domain_->eraseADD_REAL3_EXPR_REAL3_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putADD_REAL3_EXPR_REAL3_EXPR(dc, upd_dom);
                        //this->interp2domain_->putADD_REAL3_EXPR_REAL3_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::LMUL_REAL1_EXPR_REAL3_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getLMUL_REAL1_EXPR_REAL3_EXPR(dc);
                    //auto interp = this->coords2interp_->getLMUL_REAL1_EXPR_REAL3_EXPR(dc);
                    //this->coords2dom_->eraseLMUL_REAL1_EXPR_REAL3_EXPR(dc, dom);
                    //this->interp2domain_->eraseLMUL_REAL1_EXPR_REAL3_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL3_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseLMUL_REAL1_EXPR_REAL3_EXPR(dc, dom);
                        //this->interp2domain_->eraseLMUL_REAL1_EXPR_REAL3_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putLMUL_REAL1_EXPR_REAL3_EXPR(dc, upd_dom);
                        //this->interp2domain_->putLMUL_REAL1_EXPR_REAL3_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::RMUL_REAL3_EXPR_REAL1_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getRMUL_REAL3_EXPR_REAL1_EXPR(dc);
                    //auto interp = this->coords2interp_->getRMUL_REAL3_EXPR_REAL1_EXPR(dc);
                    //this->coords2dom_->eraseRMUL_REAL3_EXPR_REAL1_EXPR(dc, dom);
                    //this->interp2domain_->eraseRMUL_REAL3_EXPR_REAL1_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL3_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseRMUL_REAL3_EXPR_REAL1_EXPR(dc, dom);
                        //this->interp2domain_->eraseRMUL_REAL3_EXPR_REAL1_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putRMUL_REAL3_EXPR_REAL1_EXPR(dc, upd_dom);
                        //this->interp2domain_->putRMUL_REAL3_EXPR_REAL1_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::TMUL_REALMATRIX4_EXPR_REAL3_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getTMUL_REALMATRIX4_EXPR_REAL3_EXPR(dc);
                    //auto interp = this->coords2interp_->getTMUL_REALMATRIX4_EXPR_REAL3_EXPR(dc);
                    //this->coords2dom_->eraseTMUL_REALMATRIX4_EXPR_REAL3_EXPR(dc, dom);
                    //this->interp2domain_->eraseTMUL_REALMATRIX4_EXPR_REAL3_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL3_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseTMUL_REALMATRIX4_EXPR_REAL3_EXPR(dc, dom);
                        //this->interp2domain_->eraseTMUL_REALMATRIX4_EXPR_REAL3_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putTMUL_REALMATRIX4_EXPR_REAL3_EXPR(dc, upd_dom);
                        //this->interp2domain_->putTMUL_REALMATRIX4_EXPR_REAL3_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::LREF_REAL3_VAR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getLREF_REAL3_VAR(dc);
                    //auto interp = this->coords2interp_->getLREF_REAL3_VAR(dc);
                    //this->coords2dom_->eraseLREF_REAL3_VAR(dc, dom);
                    //this->interp2domain_->eraseLREF_REAL3_VAR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL3_LEXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseLREF_REAL3_VAR(dc, dom);
                        //this->interp2domain_->eraseLREF_REAL3_VAR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putLREF_REAL3_VAR(dc, upd_dom);
                        //this->interp2domain_->putLREF_REAL3_VAR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REF_REAL1_VAR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREF_REAL1_VAR(dc);
                    //auto interp = this->coords2interp_->getREF_REAL1_VAR(dc);
                    //this->coords2dom_->eraseREF_REAL1_VAR(dc, dom);
                    //this->interp2domain_->eraseREF_REAL1_VAR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL1_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREF_REAL1_VAR(dc, dom);
                        //this->interp2domain_->eraseREF_REAL1_VAR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREF_REAL1_VAR(dc, upd_dom);
                        //this->interp2domain_->putREF_REAL1_VAR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::ADD_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getADD_REAL1_EXPR_REAL1_EXPR(dc);
                    //auto interp = this->coords2interp_->getADD_REAL1_EXPR_REAL1_EXPR(dc);
                    //this->coords2dom_->eraseADD_REAL1_EXPR_REAL1_EXPR(dc, dom);
                    //this->interp2domain_->eraseADD_REAL1_EXPR_REAL1_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL1_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseADD_REAL1_EXPR_REAL1_EXPR(dc, dom);
                        //this->interp2domain_->eraseADD_REAL1_EXPR_REAL1_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putADD_REAL1_EXPR_REAL1_EXPR(dc, upd_dom);
                        //this->interp2domain_->putADD_REAL1_EXPR_REAL1_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::MUL_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getMUL_REAL1_EXPR_REAL1_EXPR(dc);
                    //auto interp = this->coords2interp_->getMUL_REAL1_EXPR_REAL1_EXPR(dc);
                    //this->coords2dom_->eraseMUL_REAL1_EXPR_REAL1_EXPR(dc, dom);
                    //this->interp2domain_->eraseMUL_REAL1_EXPR_REAL1_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL1_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseMUL_REAL1_EXPR_REAL1_EXPR(dc, dom);
                        //this->interp2domain_->eraseMUL_REAL1_EXPR_REAL1_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putMUL_REAL1_EXPR_REAL1_EXPR(dc, upd_dom);
                        //this->interp2domain_->putMUL_REAL1_EXPR_REAL1_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::BOOL_VAR_IDENT*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getBOOL_VAR_IDENT(dc);
                    //auto interp = this->coords2interp_->getBOOL_VAR_IDENT(dc);
                    //this->coords2dom_->eraseBOOL_VAR_IDENT(dc, dom);
                    //this->interp2domain_->eraseBOOL_VAR_IDENT(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForBOOL_VAR_IDENT(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseBOOL_VAR_IDENT(dc, dom);
                        //this->interp2domain_->eraseBOOL_VAR_IDENT(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putBOOL_VAR_IDENT(dc, upd_dom);
                        //this->interp2domain_->putBOOL_VAR_IDENT(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREAL1_VAR_IDENT(dc);
                    //auto interp = this->coords2interp_->getREAL1_VAR_IDENT(dc);
                    //this->coords2dom_->eraseREAL1_VAR_IDENT(dc, dom);
                    //this->interp2domain_->eraseREAL1_VAR_IDENT(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL1_VAR_IDENT(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREAL1_VAR_IDENT(dc, dom);
                        //this->interp2domain_->eraseREAL1_VAR_IDENT(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREAL1_VAR_IDENT(dc, upd_dom);
                        //this->interp2domain_->putREAL1_VAR_IDENT(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREAL3_VAR_IDENT(dc);
                    //auto interp = this->coords2interp_->getREAL3_VAR_IDENT(dc);
                    //this->coords2dom_->eraseREAL3_VAR_IDENT(dc, dom);
                    //this->interp2domain_->eraseREAL3_VAR_IDENT(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL3_VAR_IDENT(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREAL3_VAR_IDENT(dc, dom);
                        //this->interp2domain_->eraseREAL3_VAR_IDENT(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREAL3_VAR_IDENT(dc, upd_dom);
                        //this->interp2domain_->putREAL3_VAR_IDENT(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREAL4_VAR_IDENT(dc);
                    //auto interp = this->coords2interp_->getREAL4_VAR_IDENT(dc);
                    //this->coords2dom_->eraseREAL4_VAR_IDENT(dc, dom);
                    //this->interp2domain_->eraseREAL4_VAR_IDENT(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL4_VAR_IDENT(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREAL4_VAR_IDENT(dc, dom);
                        //this->interp2domain_->eraseREAL4_VAR_IDENT(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREAL4_VAR_IDENT(dc, upd_dom);
                        //this->interp2domain_->putREAL4_VAR_IDENT(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REALMATRIX4_VAR_IDENT*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREALMATRIX4_VAR_IDENT(dc);
                    //auto interp = this->coords2interp_->getREALMATRIX4_VAR_IDENT(dc);
                    //this->coords2dom_->eraseREALMATRIX4_VAR_IDENT(dc, dom);
                    //this->interp2domain_->eraseREALMATRIX4_VAR_IDENT(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREALMATRIX4_VAR_IDENT(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREALMATRIX4_VAR_IDENT(dc, dom);
                        //this->interp2domain_->eraseREALMATRIX4_VAR_IDENT(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREALMATRIX4_VAR_IDENT(dc, upd_dom);
                        //this->interp2domain_->putREALMATRIX4_VAR_IDENT(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REAL4_EMPTY*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREAL4_EMPTY(dc);
                    //auto interp = this->coords2interp_->getREAL4_EMPTY(dc);
                    //this->coords2dom_->eraseREAL4_EMPTY(dc, dom);
                    //this->interp2domain_->eraseREAL4_EMPTY(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL4_LITERAL(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREAL4_EMPTY(dc, dom);
                        //this->interp2domain_->eraseREAL4_EMPTY(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREAL4_EMPTY(dc, upd_dom);
                        //this->interp2domain_->putREAL4_EMPTY(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc);
                    //auto interp = this->coords2interp_->getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc);
                    //this->coords2dom_->eraseREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc, dom);
                    //this->interp2domain_->eraseREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL3_LITERAL(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc, dom);
                        //this->interp2domain_->eraseREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc, upd_dom);
                        //this->interp2domain_->putREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REAL3_EMPTY*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREAL3_EMPTY(dc);
                    //auto interp = this->coords2interp_->getREAL3_EMPTY(dc);
                    //this->coords2dom_->eraseREAL3_EMPTY(dc, dom);
                    //this->interp2domain_->eraseREAL3_EMPTY(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL3_LITERAL(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREAL3_EMPTY(dc, dom);
                        //this->interp2domain_->eraseREAL3_EMPTY(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREAL3_EMPTY(dc, upd_dom);
                        //this->interp2domain_->putREAL3_EMPTY(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REAL1_LIT*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREAL1_LIT(dc);
                    //auto interp = this->coords2interp_->getREAL1_LIT(dc);
                    //this->coords2dom_->eraseREAL1_LIT(dc, dom);
                    //this->interp2domain_->eraseREAL1_LIT(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL1_LITERAL(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREAL1_LIT(dc, dom);
                        //this->interp2domain_->eraseREAL1_LIT(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREAL1_LIT(dc, upd_dom);
                        //this->interp2domain_->putREAL1_LIT(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REALMATRIX4_EMPTY*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREALMATRIX4_EMPTY(dc);
                    //auto interp = this->coords2interp_->getREALMATRIX4_EMPTY(dc);
                    //this->coords2dom_->eraseREALMATRIX4_EMPTY(dc, dom);
                    //this->interp2domain_->eraseREALMATRIX4_EMPTY(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREALMATRIX4_LITERAL(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREALMATRIX4_EMPTY(dc, dom);
                        //this->interp2domain_->eraseREALMATRIX4_EMPTY(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREALMATRIX4_EMPTY(dc, upd_dom);
                        //this->interp2domain_->putREALMATRIX4_EMPTY(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(dc);
                    //auto interp = this->coords2interp_->getREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(dc);
                    //this->coords2dom_->eraseREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(dc, dom);
                    //this->interp2domain_->eraseREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREALMATRIX4_LITERAL(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(dc, dom);
                        //this->interp2domain_->eraseREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(dc, upd_dom);
                        //this->interp2domain_->putREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::R4R3_LIT_REAL4_EXPR_REAL3_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getR4R3_LIT_REAL4_EXPR_REAL3_EXPR(dc);
                    //auto interp = this->coords2interp_->getR4R3_LIT_REAL4_EXPR_REAL3_EXPR(dc);
                    //this->coords2dom_->eraseR4R3_LIT_REAL4_EXPR_REAL3_EXPR(dc, dom);
                    //this->interp2domain_->eraseR4R3_LIT_REAL4_EXPR_REAL3_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREALMATRIX4_LITERAL(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseR4R3_LIT_REAL4_EXPR_REAL3_EXPR(dc, dom);
                        //this->interp2domain_->eraseR4R3_LIT_REAL4_EXPR_REAL3_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putR4R3_LIT_REAL4_EXPR_REAL3_EXPR(dc, upd_dom);
                        //this->interp2domain_->putR4R3_LIT_REAL4_EXPR_REAL3_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }
            }
            printChoices();
            checker_->CheckPoll();
            std::cout << "********************************************\n";
            std::cout << "********************************************\n";
            //std::cout << "********************************************\n";
            std::cout << "See type-checking output in /peirce/phys/deps/orig/PeirceOutput.lean\n";
            std::cout << "********************************************\n";
            std::cout << "********************************************\n";
            //std::cout << "********************************************\n";
            std::cout<<"Enter -1 to print Available Spaces\n";
            std::cout<<"Enter -2 to create a New Space\n";
            std::cout<<"Enter -3 to print Available Frames\n";
            std::cout<<"Enter -4 to create a New Frame\n";
            std::cout<<"Enter -5 to print available Measurement Systems\n";
            std::cout<<"Enter -6  to create a Measurement System\n";
            std::cout<<"Enter -7 to print available Axis Orientations\n";
            std::cout<<"Enter -8  to create an Axis Orientation\n";

            std::cout<<"Enter 0 to print the Variable Table again.\n";
            std::cout << "Enter the index of a Variable to update its physical type. Enter " << sz << " to exit and check." << std::endl;
            std::cin >> choice;
        choice_buffer->push_back(std::to_string(choice));
            std::cout << std::to_string(choice) << "\n";
        }
    }
    catch(std::exception ex){
        std::cout<<ex.what()<<"\n";
    }
    printChoices();
};

void remap(coords::Coords c, domain::DomainObject newinterp){
    return;
};

