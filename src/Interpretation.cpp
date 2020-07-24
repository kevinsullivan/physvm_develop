
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
#include "Checker.h"

//#include <g3log/g3log.hpp>
#include <unordered_map>

using namespace interp;

Interpretation::Interpretation() { 
    domain_ = new domain::Domain();
    oracle_ = new oracle::Oracle_AskAll(domain_); 
    /* 
    context_ can only be set later, once Clang starts parse
    */
    ast2coords_ = new ast2coords::ASTToCoords(); 
    coords2dom_ = new coords2domain::CoordsToDomain();
    coords2interp_ = new coords2interp::CoordsToInterp();
    interp2domain_ = new interp2domain::InterpToDomain();
    checker_ = new Checker(this);
}



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
        auto p = coords2interp_->getGLOBALSTMT(op);
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
        retval += "\n" + interp_->toStringLinked(this->getSpaceInterps(), this->getSpaceNames(), this->getFrameInterps(), this->getFrameNames(), true) + "\n";

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
void Interpretation::mkMAIN_STMT(const ast::MAIN_STMT * ast ,ast::STMT* operand1) {

	coords::STMT* operand1_coords = static_cast<coords::STMT*>(ast2coords_->getStmtCoords(operand1));

    coords::MAIN_STMT* coords = ast2coords_->mkMAIN_STMT(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getSTMT(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putMAIN_STMT(coords, dom);

	interp::STMT* operand1_interp = coords2interp_->getSTMT(operand1_coords);

    interp::MAIN_STMT* interp = new interp::MAIN_STMT(coords, dom, operand1_interp);
    coords2interp_->putMAIN_STMT(coords, interp);
    interp2domain_->putMAIN_STMT(interp, dom); 
	this->GLOBALSTMT_vec.push_back(coords);

} 

void Interpretation::mkFUNCTION_STMT(const ast::FUNCTION_STMT * ast ,ast::STMT* operand1) {

	coords::STMT* operand1_coords = static_cast<coords::STMT*>(ast2coords_->getStmtCoords(operand1));

    coords::FUNCTION_STMT* coords = ast2coords_->mkFUNCTION_STMT(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getSTMT(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putFUNCTION_STMT(coords, dom);

	interp::STMT* operand1_interp = coords2interp_->getSTMT(operand1_coords);

    interp::FUNCTION_STMT* interp = new interp::FUNCTION_STMT(coords, dom, operand1_interp);
    coords2interp_->putFUNCTION_STMT(coords, interp);
    interp2domain_->putFUNCTION_STMT(interp, dom); 
	this->GLOBALSTMT_vec.push_back(coords);

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
        auto p = coords2interp_->getSTMT(op);
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
        retval += "\n" + interp_->toString() + "\n";
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
void Interpretation::mkIFTHEN_EXPR_STMT(const ast::IFTHEN_EXPR_STMT * ast ,ast::EXPR* operand1,ast::STMT* operand2) {

	coords::EXPR* operand1_coords = static_cast<coords::EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::STMT* operand2_coords = static_cast<coords::STMT*>(ast2coords_->getStmtCoords(operand2));

    coords::IFTHEN_EXPR_STMT* coords = ast2coords_->mkIFTHEN_EXPR_STMT(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getEXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getSTMT(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putIFTHEN_EXPR_STMT(coords, dom);

	interp::EXPR* operand1_interp = coords2interp_->getEXPR(operand1_coords);;
	interp::STMT* operand2_interp = coords2interp_->getSTMT(operand2_coords);

    interp::IFTHEN_EXPR_STMT* interp = new interp::IFTHEN_EXPR_STMT(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putIFTHEN_EXPR_STMT(coords, interp);
    interp2domain_->putIFTHEN_EXPR_STMT(interp, dom); 
	this->IFCOND_vec.push_back(coords);

} 

void Interpretation::mkIFTHENELSEIF_EXPR_STMT_IFCOND(const ast::IFTHENELSEIF_EXPR_STMT_IFCOND * ast ,ast::EXPR* operand1,ast::STMT* operand2,ast::IFCOND* operand3) {

	coords::EXPR* operand1_coords = static_cast<coords::EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::STMT* operand2_coords = static_cast<coords::STMT*>(ast2coords_->getStmtCoords(operand2));;
	coords::IFCOND* operand3_coords = static_cast<coords::IFCOND*>(ast2coords_->getStmtCoords(operand3));

    coords::IFTHENELSEIF_EXPR_STMT_IFCOND* coords = ast2coords_->mkIFTHENELSEIF_EXPR_STMT_IFCOND(ast, context_ ,operand1_coords,operand2_coords,operand3_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getEXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getSTMT(operand2_coords);
	domain::DomainObject* operand3_dom = coords2dom_->getIFCOND(operand3_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom,operand3_dom});
    coords2dom_->putIFTHENELSEIF_EXPR_STMT_IFCOND(coords, dom);

	interp::EXPR* operand1_interp = coords2interp_->getEXPR(operand1_coords);;
	interp::STMT* operand2_interp = coords2interp_->getSTMT(operand2_coords);;
	interp::IFCOND* operand3_interp = coords2interp_->getIFCOND(operand3_coords);

    interp::IFTHENELSEIF_EXPR_STMT_IFCOND* interp = new interp::IFTHENELSEIF_EXPR_STMT_IFCOND(coords, dom, operand1_interp,operand2_interp,operand3_interp);
    coords2interp_->putIFTHENELSEIF_EXPR_STMT_IFCOND(coords, interp);
    interp2domain_->putIFTHENELSEIF_EXPR_STMT_IFCOND(interp, dom); 
	this->IFCOND_vec.push_back(coords);

} 

void Interpretation::mkIFTHENELSE_EXPR_STMT_STMT(const ast::IFTHENELSE_EXPR_STMT_STMT * ast ,ast::EXPR* operand1,ast::STMT* operand2,ast::STMT* operand3) {

	coords::EXPR* operand1_coords = static_cast<coords::EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::STMT* operand2_coords = static_cast<coords::STMT*>(ast2coords_->getStmtCoords(operand2));;
	coords::STMT* operand3_coords = static_cast<coords::STMT*>(ast2coords_->getStmtCoords(operand3));

    coords::IFTHENELSE_EXPR_STMT_STMT* coords = ast2coords_->mkIFTHENELSE_EXPR_STMT_STMT(ast, context_ ,operand1_coords,operand2_coords,operand3_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getEXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getSTMT(operand2_coords);
	domain::DomainObject* operand3_dom = coords2dom_->getSTMT(operand3_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom,operand3_dom});
    coords2dom_->putIFTHENELSE_EXPR_STMT_STMT(coords, dom);

	interp::EXPR* operand1_interp = coords2interp_->getEXPR(operand1_coords);;
	interp::STMT* operand2_interp = coords2interp_->getSTMT(operand2_coords);;
	interp::STMT* operand3_interp = coords2interp_->getSTMT(operand3_coords);

    interp::IFTHENELSE_EXPR_STMT_STMT* interp = new interp::IFTHENELSE_EXPR_STMT_STMT(coords, dom, operand1_interp,operand2_interp,operand3_interp);
    coords2interp_->putIFTHENELSE_EXPR_STMT_STMT(coords, interp);
    interp2domain_->putIFTHENELSE_EXPR_STMT_STMT(interp, dom); 
	this->IFCOND_vec.push_back(coords);

} 


 std::string Interpretation::toString_IFCONDs(){ 
    std::vector<interp::IFCOND*> interps;
    for(auto coord : this->IFCOND_vec){
        interps.push_back(this->coords2interp_->getIFCOND(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}

 std::string Interpretation::toString_EXPRs(){ 
    std::vector<interp::EXPR*> interps;
    for(auto coord : this->EXPR_vec){
        interps.push_back(this->coords2interp_->getEXPR(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkASSIGN_REAL1_VAR_REAL1_EXPR(const ast::ASSIGN_REAL1_VAR_REAL1_EXPR * ast ,ast::REAL1_VAR_IDENT* operand1,ast::REAL1_EXPR* operand2) {

	coords::REAL1_VAR_IDENT* operand1_coords = static_cast<coords::REAL1_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));;
	coords::REAL1_EXPR* operand2_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::ASSIGN_REAL1_VAR_REAL1_EXPR* coords = ast2coords_->mkASSIGN_REAL1_VAR_REAL1_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL1_VAR_IDENT(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL1_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putASSIGN_REAL1_VAR_REAL1_EXPR(coords, dom);

	interp::REAL1_VAR_IDENT* operand1_interp = coords2interp_->getREAL1_VAR_IDENT(operand1_coords);;
	interp::REAL1_EXPR* operand2_interp = coords2interp_->getREAL1_EXPR(operand2_coords);

    interp::ASSIGN_REAL1_VAR_REAL1_EXPR* interp = new interp::ASSIGN_REAL1_VAR_REAL1_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putASSIGN_REAL1_VAR_REAL1_EXPR(coords, interp);
    interp2domain_->putASSIGN_REAL1_VAR_REAL1_EXPR(interp, dom); 
	this->ASSIGNMENT_vec.push_back(coords);

} 

void Interpretation::mkASSIGN_REAL3_VAR_REAL3_EXPR(const ast::ASSIGN_REAL3_VAR_REAL3_EXPR * ast ,ast::REAL3_VAR_IDENT* operand1,ast::REAL3_EXPR* operand2) {

	coords::REAL3_VAR_IDENT* operand1_coords = static_cast<coords::REAL3_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));;
	coords::REAL3_EXPR* operand2_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::ASSIGN_REAL3_VAR_REAL3_EXPR* coords = ast2coords_->mkASSIGN_REAL3_VAR_REAL3_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL3_VAR_IDENT(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL3_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putASSIGN_REAL3_VAR_REAL3_EXPR(coords, dom);

	interp::REAL3_VAR_IDENT* operand1_interp = coords2interp_->getREAL3_VAR_IDENT(operand1_coords);;
	interp::REAL3_EXPR* operand2_interp = coords2interp_->getREAL3_EXPR(operand2_coords);

    interp::ASSIGN_REAL3_VAR_REAL3_EXPR* interp = new interp::ASSIGN_REAL3_VAR_REAL3_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putASSIGN_REAL3_VAR_REAL3_EXPR(coords, interp);
    interp2domain_->putASSIGN_REAL3_VAR_REAL3_EXPR(interp, dom); 
	this->ASSIGNMENT_vec.push_back(coords);

} 

void Interpretation::mkASSIGN_REAL4_VAR_REAL4_EXPR(const ast::ASSIGN_REAL4_VAR_REAL4_EXPR * ast ,ast::REAL4_VAR_IDENT* operand1,ast::REAL4_EXPR* operand2) {

	coords::REAL4_VAR_IDENT* operand1_coords = static_cast<coords::REAL4_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));;
	coords::REAL4_EXPR* operand2_coords = static_cast<coords::REAL4_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::ASSIGN_REAL4_VAR_REAL4_EXPR* coords = ast2coords_->mkASSIGN_REAL4_VAR_REAL4_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL4_VAR_IDENT(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL4_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putASSIGN_REAL4_VAR_REAL4_EXPR(coords, dom);

	interp::REAL4_VAR_IDENT* operand1_interp = coords2interp_->getREAL4_VAR_IDENT(operand1_coords);;
	interp::REAL4_EXPR* operand2_interp = coords2interp_->getREAL4_EXPR(operand2_coords);

    interp::ASSIGN_REAL4_VAR_REAL4_EXPR* interp = new interp::ASSIGN_REAL4_VAR_REAL4_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putASSIGN_REAL4_VAR_REAL4_EXPR(coords, interp);
    interp2domain_->putASSIGN_REAL4_VAR_REAL4_EXPR(interp, dom); 
	this->ASSIGNMENT_vec.push_back(coords);

} 

void Interpretation::mkASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(const ast::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR * ast ,ast::REALMATRIX_VAR_IDENT* operand1,ast::REALMATRIX_EXPR* operand2) {

	coords::REALMATRIX_VAR_IDENT* operand1_coords = static_cast<coords::REALMATRIX_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));;
	coords::REALMATRIX_EXPR* operand2_coords = static_cast<coords::REALMATRIX_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* coords = ast2coords_->mkASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREALMATRIX_VAR_IDENT(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREALMATRIX_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(coords, dom);

	interp::REALMATRIX_VAR_IDENT* operand1_interp = coords2interp_->getREALMATRIX_VAR_IDENT(operand1_coords);;
	interp::REALMATRIX_EXPR* operand2_interp = coords2interp_->getREALMATRIX_EXPR(operand2_coords);

    interp::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* interp = new interp::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(coords, interp);
    interp2domain_->putASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(interp, dom); 
	this->ASSIGNMENT_vec.push_back(coords);

} 


 std::string Interpretation::toString_ASSIGNMENTs(){ 
    std::vector<interp::ASSIGNMENT*> interps;
    for(auto coord : this->ASSIGNMENT_vec){
        interps.push_back(this->coords2interp_->getASSIGNMENT(coord));
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

void Interpretation::mkDECL_REALMATRIX_VAR_REALMATRIX_EXPR(const ast::DECL_REALMATRIX_VAR_REALMATRIX_EXPR * ast ,ast::REALMATRIX_VAR_IDENT* operand1,ast::REALMATRIX_EXPR* operand2) {

	coords::REALMATRIX_VAR_IDENT* operand1_coords = static_cast<coords::REALMATRIX_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));;
	coords::REALMATRIX_EXPR* operand2_coords = static_cast<coords::REALMATRIX_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* coords = ast2coords_->mkDECL_REALMATRIX_VAR_REALMATRIX_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREALMATRIX_VAR_IDENT(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREALMATRIX_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putDECL_REALMATRIX_VAR_REALMATRIX_EXPR(coords, dom);

	interp::REALMATRIX_VAR_IDENT* operand1_interp = coords2interp_->getREALMATRIX_VAR_IDENT(operand1_coords);;
	interp::REALMATRIX_EXPR* operand2_interp = coords2interp_->getREALMATRIX_EXPR(operand2_coords);

    interp::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* interp = new interp::DECL_REALMATRIX_VAR_REALMATRIX_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putDECL_REALMATRIX_VAR_REALMATRIX_EXPR(coords, interp);
    interp2domain_->putDECL_REALMATRIX_VAR_REALMATRIX_EXPR(interp, dom); 
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

void Interpretation::mkDECL_REALMATRIX_VAR(const ast::DECL_REALMATRIX_VAR * ast ,ast::REALMATRIX_VAR_IDENT* operand1) {

	coords::REALMATRIX_VAR_IDENT* operand1_coords = static_cast<coords::REALMATRIX_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));

    coords::DECL_REALMATRIX_VAR* coords = ast2coords_->mkDECL_REALMATRIX_VAR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREALMATRIX_VAR_IDENT(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putDECL_REALMATRIX_VAR(coords, dom);

	interp::REALMATRIX_VAR_IDENT* operand1_interp = coords2interp_->getREALMATRIX_VAR_IDENT(operand1_coords);

    interp::DECL_REALMATRIX_VAR* interp = new interp::DECL_REALMATRIX_VAR(coords, dom, operand1_interp);
    coords2interp_->putDECL_REALMATRIX_VAR(coords, interp);
    interp2domain_->putDECL_REALMATRIX_VAR(interp, dom); 
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
void Interpretation::mkPAREN_REAL1_EXPR(const ast::PAREN_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1) {

	coords::REAL1_EXPR* operand1_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand1));

    coords::PAREN_REAL1_EXPR* coords = ast2coords_->mkPAREN_REAL1_EXPR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL1_EXPR(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putPAREN_REAL1_EXPR(coords, dom);

	interp::REAL1_EXPR* operand1_interp = coords2interp_->getREAL1_EXPR(operand1_coords);

    interp::PAREN_REAL1_EXPR* interp = new interp::PAREN_REAL1_EXPR(coords, dom, operand1_interp);
    coords2interp_->putPAREN_REAL1_EXPR(coords, interp);
    interp2domain_->putPAREN_REAL1_EXPR(interp, dom); 
	this->REAL1_EXPR_vec.push_back(coords);

} 

void Interpretation::mkINV_REAL1_EXPR(const ast::INV_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1) {

	coords::REAL1_EXPR* operand1_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand1));

    coords::INV_REAL1_EXPR* coords = ast2coords_->mkINV_REAL1_EXPR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL1_EXPR(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putINV_REAL1_EXPR(coords, dom);

	interp::REAL1_EXPR* operand1_interp = coords2interp_->getREAL1_EXPR(operand1_coords);

    interp::INV_REAL1_EXPR* interp = new interp::INV_REAL1_EXPR(coords, dom, operand1_interp);
    coords2interp_->putINV_REAL1_EXPR(coords, interp);
    interp2domain_->putINV_REAL1_EXPR(interp, dom); 
	this->REAL1_EXPR_vec.push_back(coords);

} 

void Interpretation::mkNEG_REAL1_EXPR(const ast::NEG_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1) {

	coords::REAL1_EXPR* operand1_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand1));

    coords::NEG_REAL1_EXPR* coords = ast2coords_->mkNEG_REAL1_EXPR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL1_EXPR(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putNEG_REAL1_EXPR(coords, dom);

	interp::REAL1_EXPR* operand1_interp = coords2interp_->getREAL1_EXPR(operand1_coords);

    interp::NEG_REAL1_EXPR* interp = new interp::NEG_REAL1_EXPR(coords, dom, operand1_interp);
    coords2interp_->putNEG_REAL1_EXPR(coords, interp);
    interp2domain_->putNEG_REAL1_EXPR(interp, dom); 
	this->REAL1_EXPR_vec.push_back(coords);

} 

void Interpretation::mkADD_REAL1_EXPR_REAL1_EXPR(const ast::ADD_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2) {

	coords::REAL1_EXPR* operand1_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL1_EXPR* operand2_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::ADD_REAL1_EXPR_REAL1_EXPR* coords = ast2coords_->mkADD_REAL1_EXPR_REAL1_EXPR(ast, context_ ,operand1_coords,operand2_coords);

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

void Interpretation::mkSUB_REAL1_EXPR_REAL1_EXPR(const ast::SUB_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2) {

	coords::REAL1_EXPR* operand1_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL1_EXPR* operand2_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::SUB_REAL1_EXPR_REAL1_EXPR* coords = ast2coords_->mkSUB_REAL1_EXPR_REAL1_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL1_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL1_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putSUB_REAL1_EXPR_REAL1_EXPR(coords, dom);

	interp::REAL1_EXPR* operand1_interp = coords2interp_->getREAL1_EXPR(operand1_coords);;
	interp::REAL1_EXPR* operand2_interp = coords2interp_->getREAL1_EXPR(operand2_coords);

    interp::SUB_REAL1_EXPR_REAL1_EXPR* interp = new interp::SUB_REAL1_EXPR_REAL1_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putSUB_REAL1_EXPR_REAL1_EXPR(coords, interp);
    interp2domain_->putSUB_REAL1_EXPR_REAL1_EXPR(interp, dom); 
	this->REAL1_EXPR_vec.push_back(coords);

} 

void Interpretation::mkMUL_REAL1_EXPR_REAL1_EXPR(const ast::MUL_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2) {

	coords::REAL1_EXPR* operand1_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL1_EXPR* operand2_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::MUL_REAL1_EXPR_REAL1_EXPR* coords = ast2coords_->mkMUL_REAL1_EXPR_REAL1_EXPR(ast, context_ ,operand1_coords,operand2_coords);

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

void Interpretation::mkDIV_REAL1_EXPR_REAL1_EXPR(const ast::DIV_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2) {

	coords::REAL1_EXPR* operand1_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL1_EXPR* operand2_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::DIV_REAL1_EXPR_REAL1_EXPR* coords = ast2coords_->mkDIV_REAL1_EXPR_REAL1_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL1_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL1_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putDIV_REAL1_EXPR_REAL1_EXPR(coords, dom);

	interp::REAL1_EXPR* operand1_interp = coords2interp_->getREAL1_EXPR(operand1_coords);;
	interp::REAL1_EXPR* operand2_interp = coords2interp_->getREAL1_EXPR(operand2_coords);

    interp::DIV_REAL1_EXPR_REAL1_EXPR* interp = new interp::DIV_REAL1_EXPR_REAL1_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putDIV_REAL1_EXPR_REAL1_EXPR(coords, interp);
    interp2domain_->putDIV_REAL1_EXPR_REAL1_EXPR(interp, dom); 
	this->REAL1_EXPR_vec.push_back(coords);

} 

void Interpretation::mkREF_REAL1_VAR(const ast::REF_REAL1_VAR * ast ,ast::REAL1_VAR_IDENT* operand1) {

	coords::REAL1_VAR_IDENT* operand1_coords = static_cast<coords::REAL1_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));

    coords::REF_REAL1_VAR* coords = ast2coords_->mkREF_REAL1_VAR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL1_VAR_IDENT(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putREF_REAL1_VAR(coords, dom);

	interp::REAL1_VAR_IDENT* operand1_interp = coords2interp_->getREAL1_VAR_IDENT(operand1_coords);

    interp::REF_REAL1_VAR* interp = new interp::REF_REAL1_VAR(coords, dom, operand1_interp);
    coords2interp_->putREF_REAL1_VAR(coords, interp);
    interp2domain_->putREF_REAL1_VAR(interp, dom); 
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
void Interpretation::mkPAREN_REAL3_EXPR(const ast::PAREN_REAL3_EXPR * ast ,ast::REAL3_EXPR* operand1) {

	coords::REAL3_EXPR* operand1_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand1));

    coords::PAREN_REAL3_EXPR* coords = ast2coords_->mkPAREN_REAL3_EXPR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL3_EXPR(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putPAREN_REAL3_EXPR(coords, dom);

	interp::REAL3_EXPR* operand1_interp = coords2interp_->getREAL3_EXPR(operand1_coords);

    interp::PAREN_REAL3_EXPR* interp = new interp::PAREN_REAL3_EXPR(coords, dom, operand1_interp);
    coords2interp_->putPAREN_REAL3_EXPR(coords, interp);
    interp2domain_->putPAREN_REAL3_EXPR(interp, dom); 
	this->REAL3_EXPR_vec.push_back(coords);

} 

void Interpretation::mkADD_REAL3_EXPR_REAL3_EXPR(const ast::ADD_REAL3_EXPR_REAL3_EXPR * ast ,ast::REAL3_EXPR* operand1,ast::REAL3_EXPR* operand2) {

	coords::REAL3_EXPR* operand1_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL3_EXPR* operand2_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::ADD_REAL3_EXPR_REAL3_EXPR* coords = ast2coords_->mkADD_REAL3_EXPR_REAL3_EXPR(ast, context_ ,operand1_coords,operand2_coords);

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

void Interpretation::mkSUB_REAL3_EXPR_REAL3_EXPR(const ast::SUB_REAL3_EXPR_REAL3_EXPR * ast ,ast::REAL3_EXPR* operand1,ast::REAL3_EXPR* operand2) {

	coords::REAL3_EXPR* operand1_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL3_EXPR* operand2_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::SUB_REAL3_EXPR_REAL3_EXPR* coords = ast2coords_->mkSUB_REAL3_EXPR_REAL3_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL3_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL3_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putSUB_REAL3_EXPR_REAL3_EXPR(coords, dom);

	interp::REAL3_EXPR* operand1_interp = coords2interp_->getREAL3_EXPR(operand1_coords);;
	interp::REAL3_EXPR* operand2_interp = coords2interp_->getREAL3_EXPR(operand2_coords);

    interp::SUB_REAL3_EXPR_REAL3_EXPR* interp = new interp::SUB_REAL3_EXPR_REAL3_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putSUB_REAL3_EXPR_REAL3_EXPR(coords, interp);
    interp2domain_->putSUB_REAL3_EXPR_REAL3_EXPR(interp, dom); 
	this->REAL3_EXPR_vec.push_back(coords);

} 

void Interpretation::mkINV_REAL3_EXPR(const ast::INV_REAL3_EXPR * ast ,ast::REAL3_EXPR* operand1) {

	coords::REAL3_EXPR* operand1_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand1));

    coords::INV_REAL3_EXPR* coords = ast2coords_->mkINV_REAL3_EXPR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL3_EXPR(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putINV_REAL3_EXPR(coords, dom);

	interp::REAL3_EXPR* operand1_interp = coords2interp_->getREAL3_EXPR(operand1_coords);

    interp::INV_REAL3_EXPR* interp = new interp::INV_REAL3_EXPR(coords, dom, operand1_interp);
    coords2interp_->putINV_REAL3_EXPR(coords, interp);
    interp2domain_->putINV_REAL3_EXPR(interp, dom); 
	this->REAL3_EXPR_vec.push_back(coords);

} 

void Interpretation::mkNEG_REAL3_EXPR(const ast::NEG_REAL3_EXPR * ast ,ast::REAL3_EXPR* operand1) {

	coords::REAL3_EXPR* operand1_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand1));

    coords::NEG_REAL3_EXPR* coords = ast2coords_->mkNEG_REAL3_EXPR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL3_EXPR(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putNEG_REAL3_EXPR(coords, dom);

	interp::REAL3_EXPR* operand1_interp = coords2interp_->getREAL3_EXPR(operand1_coords);

    interp::NEG_REAL3_EXPR* interp = new interp::NEG_REAL3_EXPR(coords, dom, operand1_interp);
    coords2interp_->putNEG_REAL3_EXPR(coords, interp);
    interp2domain_->putNEG_REAL3_EXPR(interp, dom); 
	this->REAL3_EXPR_vec.push_back(coords);

} 

void Interpretation::mkMUL_REAL3_EXPR_REAL1_EXPR(const ast::MUL_REAL3_EXPR_REAL1_EXPR * ast ,ast::REAL3_EXPR* operand1,ast::REAL1_EXPR* operand2) {

	coords::REAL3_EXPR* operand1_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL1_EXPR* operand2_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::MUL_REAL3_EXPR_REAL1_EXPR* coords = ast2coords_->mkMUL_REAL3_EXPR_REAL1_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL3_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL1_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putMUL_REAL3_EXPR_REAL1_EXPR(coords, dom);

	interp::REAL3_EXPR* operand1_interp = coords2interp_->getREAL3_EXPR(operand1_coords);;
	interp::REAL1_EXPR* operand2_interp = coords2interp_->getREAL1_EXPR(operand2_coords);

    interp::MUL_REAL3_EXPR_REAL1_EXPR* interp = new interp::MUL_REAL3_EXPR_REAL1_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putMUL_REAL3_EXPR_REAL1_EXPR(coords, interp);
    interp2domain_->putMUL_REAL3_EXPR_REAL1_EXPR(interp, dom); 
	this->REAL3_EXPR_vec.push_back(coords);

} 

void Interpretation::mkMUL_REALMATRIX_EXPR_REAL3_EXPR(const ast::MUL_REALMATRIX_EXPR_REAL3_EXPR * ast ,ast::REALMATRIX_EXPR* operand1,ast::REAL3_EXPR* operand2) {

	coords::REALMATRIX_EXPR* operand1_coords = static_cast<coords::REALMATRIX_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL3_EXPR* operand2_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::MUL_REALMATRIX_EXPR_REAL3_EXPR* coords = ast2coords_->mkMUL_REALMATRIX_EXPR_REAL3_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREALMATRIX_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL3_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putMUL_REALMATRIX_EXPR_REAL3_EXPR(coords, dom);

	interp::REALMATRIX_EXPR* operand1_interp = coords2interp_->getREALMATRIX_EXPR(operand1_coords);;
	interp::REAL3_EXPR* operand2_interp = coords2interp_->getREAL3_EXPR(operand2_coords);

    interp::MUL_REALMATRIX_EXPR_REAL3_EXPR* interp = new interp::MUL_REALMATRIX_EXPR_REAL3_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putMUL_REALMATRIX_EXPR_REAL3_EXPR(coords, interp);
    interp2domain_->putMUL_REALMATRIX_EXPR_REAL3_EXPR(interp, dom); 
	this->REAL3_EXPR_vec.push_back(coords);

} 

void Interpretation::mkDIV_REAL3_EXPR_REAL1_EXPR(const ast::DIV_REAL3_EXPR_REAL1_EXPR * ast ,ast::REAL3_EXPR* operand1,ast::REAL1_EXPR* operand2) {

	coords::REAL3_EXPR* operand1_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL1_EXPR* operand2_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::DIV_REAL3_EXPR_REAL1_EXPR* coords = ast2coords_->mkDIV_REAL3_EXPR_REAL1_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL3_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL1_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putDIV_REAL3_EXPR_REAL1_EXPR(coords, dom);

	interp::REAL3_EXPR* operand1_interp = coords2interp_->getREAL3_EXPR(operand1_coords);;
	interp::REAL1_EXPR* operand2_interp = coords2interp_->getREAL1_EXPR(operand2_coords);

    interp::DIV_REAL3_EXPR_REAL1_EXPR* interp = new interp::DIV_REAL3_EXPR_REAL1_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putDIV_REAL3_EXPR_REAL1_EXPR(coords, interp);
    interp2domain_->putDIV_REAL3_EXPR_REAL1_EXPR(interp, dom); 
	this->REAL3_EXPR_vec.push_back(coords);

} 

void Interpretation::mkREF_REAL3_VAR(const ast::REF_REAL3_VAR * ast ,ast::REAL3_VAR_IDENT* operand1) {

	coords::REAL3_VAR_IDENT* operand1_coords = static_cast<coords::REAL3_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));

    coords::REF_REAL3_VAR* coords = ast2coords_->mkREF_REAL3_VAR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL3_VAR_IDENT(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putREF_REAL3_VAR(coords, dom);

	interp::REAL3_VAR_IDENT* operand1_interp = coords2interp_->getREAL3_VAR_IDENT(operand1_coords);

    interp::REF_REAL3_VAR* interp = new interp::REF_REAL3_VAR(coords, dom, operand1_interp);
    coords2interp_->putREF_REAL3_VAR(coords, interp);
    interp2domain_->putREF_REAL3_VAR(interp, dom); 
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
void Interpretation::mkPAREN_REAL4_EXPR(const ast::PAREN_REAL4_EXPR * ast ,ast::REAL4_EXPR* operand1) {

	coords::REAL4_EXPR* operand1_coords = static_cast<coords::REAL4_EXPR*>(ast2coords_->getStmtCoords(operand1));

    coords::PAREN_REAL4_EXPR* coords = ast2coords_->mkPAREN_REAL4_EXPR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL4_EXPR(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putPAREN_REAL4_EXPR(coords, dom);

	interp::REAL4_EXPR* operand1_interp = coords2interp_->getREAL4_EXPR(operand1_coords);

    interp::PAREN_REAL4_EXPR* interp = new interp::PAREN_REAL4_EXPR(coords, dom, operand1_interp);
    coords2interp_->putPAREN_REAL4_EXPR(coords, interp);
    interp2domain_->putPAREN_REAL4_EXPR(interp, dom); 
	this->REAL4_EXPR_vec.push_back(coords);

} 

void Interpretation::mkADD_REAL4_EXPR_REAL4_EXPR(const ast::ADD_REAL4_EXPR_REAL4_EXPR * ast ,ast::REAL4_EXPR* operand1,ast::REAL4_EXPR* operand2) {

	coords::REAL4_EXPR* operand1_coords = static_cast<coords::REAL4_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL4_EXPR* operand2_coords = static_cast<coords::REAL4_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::ADD_REAL4_EXPR_REAL4_EXPR* coords = ast2coords_->mkADD_REAL4_EXPR_REAL4_EXPR(ast, context_ ,operand1_coords,operand2_coords);

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

void Interpretation::mkMUL_REAL4_EXPR_REAL1_EXPR(const ast::MUL_REAL4_EXPR_REAL1_EXPR * ast ,ast::REAL4_EXPR* operand1,ast::REAL1_EXPR* operand2) {

	coords::REAL4_EXPR* operand1_coords = static_cast<coords::REAL4_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL1_EXPR* operand2_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::MUL_REAL4_EXPR_REAL1_EXPR* coords = ast2coords_->mkMUL_REAL4_EXPR_REAL1_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL4_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL1_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putMUL_REAL4_EXPR_REAL1_EXPR(coords, dom);

	interp::REAL4_EXPR* operand1_interp = coords2interp_->getREAL4_EXPR(operand1_coords);;
	interp::REAL1_EXPR* operand2_interp = coords2interp_->getREAL1_EXPR(operand2_coords);

    interp::MUL_REAL4_EXPR_REAL1_EXPR* interp = new interp::MUL_REAL4_EXPR_REAL1_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putMUL_REAL4_EXPR_REAL1_EXPR(coords, interp);
    interp2domain_->putMUL_REAL4_EXPR_REAL1_EXPR(interp, dom); 
	this->REAL4_EXPR_vec.push_back(coords);

} 

void Interpretation::mkREF_REAL4_VAR(const ast::REF_REAL4_VAR * ast ,ast::REAL4_VAR_IDENT* operand1) {

	coords::REAL4_VAR_IDENT* operand1_coords = static_cast<coords::REAL4_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));

    coords::REF_REAL4_VAR* coords = ast2coords_->mkREF_REAL4_VAR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL4_VAR_IDENT(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putREF_REAL4_VAR(coords, dom);

	interp::REAL4_VAR_IDENT* operand1_interp = coords2interp_->getREAL4_VAR_IDENT(operand1_coords);

    interp::REF_REAL4_VAR* interp = new interp::REF_REAL4_VAR(coords, dom, operand1_interp);
    coords2interp_->putREF_REAL4_VAR(coords, interp);
    interp2domain_->putREF_REAL4_VAR(interp, dom); 
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
void Interpretation::mkPAREN_REALMATRIX_EXPR(const ast::PAREN_REALMATRIX_EXPR * ast ,ast::REALMATRIX_EXPR* operand1) {

	coords::REALMATRIX_EXPR* operand1_coords = static_cast<coords::REALMATRIX_EXPR*>(ast2coords_->getStmtCoords(operand1));

    coords::PAREN_REALMATRIX_EXPR* coords = ast2coords_->mkPAREN_REALMATRIX_EXPR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREALMATRIX_EXPR(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putPAREN_REALMATRIX_EXPR(coords, dom);

	interp::REALMATRIX_EXPR* operand1_interp = coords2interp_->getREALMATRIX_EXPR(operand1_coords);

    interp::PAREN_REALMATRIX_EXPR* interp = new interp::PAREN_REALMATRIX_EXPR(coords, dom, operand1_interp);
    coords2interp_->putPAREN_REALMATRIX_EXPR(coords, interp);
    interp2domain_->putPAREN_REALMATRIX_EXPR(interp, dom); 
	this->REALMATRIX_EXPR_vec.push_back(coords);

} 

void Interpretation::mkMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(const ast::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR * ast ,ast::REALMATRIX_EXPR* operand1,ast::REALMATRIX_EXPR* operand2) {

	coords::REALMATRIX_EXPR* operand1_coords = static_cast<coords::REALMATRIX_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REALMATRIX_EXPR* operand2_coords = static_cast<coords::REALMATRIX_EXPR*>(ast2coords_->getStmtCoords(operand2));

    coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* coords = ast2coords_->mkMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(ast, context_ ,operand1_coords,operand2_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREALMATRIX_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREALMATRIX_EXPR(operand2_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom});
    coords2dom_->putMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(coords, dom);

	interp::REALMATRIX_EXPR* operand1_interp = coords2interp_->getREALMATRIX_EXPR(operand1_coords);;
	interp::REALMATRIX_EXPR* operand2_interp = coords2interp_->getREALMATRIX_EXPR(operand2_coords);

    interp::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* interp = new interp::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR(coords, dom, operand1_interp,operand2_interp);
    coords2interp_->putMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(coords, interp);
    interp2domain_->putMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(interp, dom); 
	this->REALMATRIX_EXPR_vec.push_back(coords);

} 

void Interpretation::mkREF_EXPR_REALMATRIX_VAR(const ast::REF_EXPR_REALMATRIX_VAR * ast ,ast::REALMATRIX_VAR_IDENT* operand1) {

	coords::REALMATRIX_VAR_IDENT* operand1_coords = static_cast<coords::REALMATRIX_VAR_IDENT*>(ast2coords_->getDeclCoords(operand1));

    coords::REF_EXPR_REALMATRIX_VAR* coords = ast2coords_->mkREF_EXPR_REALMATRIX_VAR(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREALMATRIX_VAR_IDENT(operand1_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putREF_EXPR_REALMATRIX_VAR(coords, dom);

	interp::REALMATRIX_VAR_IDENT* operand1_interp = coords2interp_->getREALMATRIX_VAR_IDENT(operand1_coords);

    interp::REF_EXPR_REALMATRIX_VAR* interp = new interp::REF_EXPR_REALMATRIX_VAR(coords, dom, operand1_interp);
    coords2interp_->putREF_EXPR_REALMATRIX_VAR(coords, interp);
    interp2domain_->putREF_EXPR_REALMATRIX_VAR(interp, dom); 
	this->REALMATRIX_EXPR_vec.push_back(coords);

} 


 std::string Interpretation::toString_REALMATRIX_EXPRs(){ 
    std::vector<interp::REALMATRIX_EXPR*> interps;
    for(auto coord : this->REALMATRIX_EXPR_vec){
        interps.push_back(this->coords2interp_->getREALMATRIX_EXPR(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkREAL1_VAR_IDENT(const ast::REAL1_VAR_IDENT * ast ) {


    coords::REAL1_VAR_IDENT* coords = ast2coords_->mkREAL1_VAR_IDENT(ast, context_ );

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
void Interpretation::mkREAL3_VAR_IDENT(const ast::REAL3_VAR_IDENT * ast ) {


    coords::REAL3_VAR_IDENT* coords = ast2coords_->mkREAL3_VAR_IDENT(ast, context_ );

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
void Interpretation::mkREAL4_VAR_IDENT(const ast::REAL4_VAR_IDENT * ast ) {


    coords::REAL4_VAR_IDENT* coords = ast2coords_->mkREAL4_VAR_IDENT(ast, context_ );

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
void Interpretation::mkREALMATRIX_VAR_IDENT(const ast::REALMATRIX_VAR_IDENT * ast ) {


    coords::REALMATRIX_VAR_IDENT* coords = ast2coords_->mkREALMATRIX_VAR_IDENT(ast, context_ );

    domain::DomainObject* dom = domain_->mkDefaultDomainContainer({});
    coords2dom_->putREALMATRIX_VAR_IDENT(coords, dom);


    interp::REALMATRIX_VAR_IDENT* interp = new interp::REALMATRIX_VAR_IDENT(coords, dom);
    coords2interp_->putREALMATRIX_VAR_IDENT(coords, interp);
    interp2domain_->putREALMATRIX_VAR_IDENT(interp, dom); 
	this->REALMATRIX_VAR_IDENT_vec.push_back(coords);

} 


 std::string Interpretation::toString_REALMATRIX_VAR_IDENTs(){ 
    std::vector<interp::REALMATRIX_VAR_IDENT*> interps;
    for(auto coord : this->REALMATRIX_VAR_IDENT_vec){
        interps.push_back(this->coords2interp_->getREALMATRIX_VAR_IDENT(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkREAL1_LITERAL1(const ast::REAL1_LITERAL1 * ast ) {


    coords::REAL1_LITERAL1* coords = ast2coords_->mkREAL1_LITERAL1(ast, context_ ,1);

    domain::DomainObject* dom = domain_->mkDefaultDomainContainer({});
    coords2dom_->putREAL1_LITERAL1(coords, dom);


    interp::REAL1_LITERAL1* interp = new interp::REAL1_LITERAL1(coords, dom);
    coords2interp_->putREAL1_LITERAL1(coords, interp);
    interp2domain_->putREAL1_LITERAL1(interp, dom); 
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
void Interpretation::mkREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(const ast::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2,ast::REAL1_EXPR* operand3) {

	coords::REAL1_EXPR* operand1_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL1_EXPR* operand2_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand2));;
	coords::REAL1_EXPR* operand3_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand3));

    coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* coords = ast2coords_->mkREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(ast, context_ ,operand1_coords,operand2_coords,operand3_coords);

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

void Interpretation::mkREAL3_LITERAL3(const ast::REAL3_LITERAL3 * ast ) {


    coords::REAL3_LITERAL3* coords = ast2coords_->mkREAL3_LITERAL3(ast, context_ ,1,2,3);

    domain::DomainObject* dom = domain_->mkDefaultDomainContainer({});
    coords2dom_->putREAL3_LITERAL3(coords, dom);


    interp::REAL3_LITERAL3* interp = new interp::REAL3_LITERAL3(coords, dom);
    coords2interp_->putREAL3_LITERAL3(coords, interp);
    interp2domain_->putREAL3_LITERAL3(interp, dom); 
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
void Interpretation::mkREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(const ast::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2,ast::REAL1_EXPR* operand3,ast::REAL1_EXPR* operand4) {

	coords::REAL1_EXPR* operand1_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL1_EXPR* operand2_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand2));;
	coords::REAL1_EXPR* operand3_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand3));;
	coords::REAL1_EXPR* operand4_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand4));

    coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* coords = ast2coords_->mkREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(ast, context_ ,operand1_coords,operand2_coords,operand3_coords,operand4_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL1_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL1_EXPR(operand2_coords);
	domain::DomainObject* operand3_dom = coords2dom_->getREAL1_EXPR(operand3_coords);
	domain::DomainObject* operand4_dom = coords2dom_->getREAL1_EXPR(operand4_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom,operand3_dom,operand4_dom});
    coords2dom_->putREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords, dom);

	interp::REAL1_EXPR* operand1_interp = coords2interp_->getREAL1_EXPR(operand1_coords);;
	interp::REAL1_EXPR* operand2_interp = coords2interp_->getREAL1_EXPR(operand2_coords);;
	interp::REAL1_EXPR* operand3_interp = coords2interp_->getREAL1_EXPR(operand3_coords);;
	interp::REAL1_EXPR* operand4_interp = coords2interp_->getREAL1_EXPR(operand4_coords);

    interp::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* interp = new interp::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords, dom, operand1_interp,operand2_interp,operand3_interp,operand4_interp);
    coords2interp_->putREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords, interp);
    interp2domain_->putREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp, dom); 
	this->REAL4_LITERAL_vec.push_back(coords);

} 

void Interpretation::mkREAL4_LITERAL4(const ast::REAL4_LITERAL4 * ast ) {


    coords::REAL4_LITERAL4* coords = ast2coords_->mkREAL4_LITERAL4(ast, context_ ,1,2,3,4);

    domain::DomainObject* dom = domain_->mkDefaultDomainContainer({});
    coords2dom_->putREAL4_LITERAL4(coords, dom);


    interp::REAL4_LITERAL4* interp = new interp::REAL4_LITERAL4(coords, dom);
    coords2interp_->putREAL4_LITERAL4(coords, interp);
    interp2domain_->putREAL4_LITERAL4(interp, dom); 
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
void Interpretation::mkREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(const ast::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR * ast ,ast::REAL3_EXPR* operand1,ast::REAL3_EXPR* operand2,ast::REAL3_EXPR* operand3) {

	coords::REAL3_EXPR* operand1_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL3_EXPR* operand2_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand2));;
	coords::REAL3_EXPR* operand3_coords = static_cast<coords::REAL3_EXPR*>(ast2coords_->getStmtCoords(operand3));

    coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* coords = ast2coords_->mkREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(ast, context_ ,operand1_coords,operand2_coords,operand3_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL3_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL3_EXPR(operand2_coords);
	domain::DomainObject* operand3_dom = coords2dom_->getREAL3_EXPR(operand3_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom,operand3_dom});
    coords2dom_->putREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(coords, dom);

	interp::REAL3_EXPR* operand1_interp = coords2interp_->getREAL3_EXPR(operand1_coords);;
	interp::REAL3_EXPR* operand2_interp = coords2interp_->getREAL3_EXPR(operand2_coords);;
	interp::REAL3_EXPR* operand3_interp = coords2interp_->getREAL3_EXPR(operand3_coords);

    interp::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* interp = new interp::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(coords, dom, operand1_interp,operand2_interp,operand3_interp);
    coords2interp_->putREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(coords, interp);
    interp2domain_->putREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(interp, dom); 
	this->REALMATRIX_LITERAL_vec.push_back(coords);

} 

void Interpretation::mkREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(const ast::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2,ast::REAL1_EXPR* operand3,ast::REAL1_EXPR* operand4,ast::REAL1_EXPR* operand5,ast::REAL1_EXPR* operand6,ast::REAL1_EXPR* operand7,ast::REAL1_EXPR* operand8,ast::REAL1_EXPR* operand9) {

	coords::REAL1_EXPR* operand1_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand1));;
	coords::REAL1_EXPR* operand2_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand2));;
	coords::REAL1_EXPR* operand3_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand3));;
	coords::REAL1_EXPR* operand4_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand4));;
	coords::REAL1_EXPR* operand5_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand5));;
	coords::REAL1_EXPR* operand6_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand6));;
	coords::REAL1_EXPR* operand7_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand7));;
	coords::REAL1_EXPR* operand8_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand8));;
	coords::REAL1_EXPR* operand9_coords = static_cast<coords::REAL1_EXPR*>(ast2coords_->getStmtCoords(operand9));

    coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* coords = ast2coords_->mkREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(ast, context_ ,operand1_coords,operand2_coords,operand3_coords,operand4_coords,operand5_coords,operand6_coords,operand7_coords,operand8_coords,operand9_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getREAL1_EXPR(operand1_coords);
	domain::DomainObject* operand2_dom = coords2dom_->getREAL1_EXPR(operand2_coords);
	domain::DomainObject* operand3_dom = coords2dom_->getREAL1_EXPR(operand3_coords);
	domain::DomainObject* operand4_dom = coords2dom_->getREAL1_EXPR(operand4_coords);
	domain::DomainObject* operand5_dom = coords2dom_->getREAL1_EXPR(operand5_coords);
	domain::DomainObject* operand6_dom = coords2dom_->getREAL1_EXPR(operand6_coords);
	domain::DomainObject* operand7_dom = coords2dom_->getREAL1_EXPR(operand7_coords);
	domain::DomainObject* operand8_dom = coords2dom_->getREAL1_EXPR(operand8_coords);
	domain::DomainObject* operand9_dom = coords2dom_->getREAL1_EXPR(operand9_coords);
    domain::DomainObject* dom =  domain_->mkDefaultDomainContainer({operand1_dom,operand2_dom,operand3_dom,operand4_dom,operand5_dom,operand6_dom,operand7_dom,operand8_dom,operand9_dom});
    coords2dom_->putREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords, dom);

	interp::REAL1_EXPR* operand1_interp = coords2interp_->getREAL1_EXPR(operand1_coords);;
	interp::REAL1_EXPR* operand2_interp = coords2interp_->getREAL1_EXPR(operand2_coords);;
	interp::REAL1_EXPR* operand3_interp = coords2interp_->getREAL1_EXPR(operand3_coords);;
	interp::REAL1_EXPR* operand4_interp = coords2interp_->getREAL1_EXPR(operand4_coords);;
	interp::REAL1_EXPR* operand5_interp = coords2interp_->getREAL1_EXPR(operand5_coords);;
	interp::REAL1_EXPR* operand6_interp = coords2interp_->getREAL1_EXPR(operand6_coords);;
	interp::REAL1_EXPR* operand7_interp = coords2interp_->getREAL1_EXPR(operand7_coords);;
	interp::REAL1_EXPR* operand8_interp = coords2interp_->getREAL1_EXPR(operand8_coords);;
	interp::REAL1_EXPR* operand9_interp = coords2interp_->getREAL1_EXPR(operand9_coords);

    interp::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* interp = new interp::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords, dom, operand1_interp,operand2_interp,operand3_interp,operand4_interp,operand5_interp,operand6_interp,operand7_interp,operand8_interp,operand9_interp);
    coords2interp_->putREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords, interp);
    interp2domain_->putREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp, dom); 
	this->REALMATRIX_LITERAL_vec.push_back(coords);

} 

void Interpretation::mkREALMATRIX_LITERAL9(const ast::REALMATRIX_LITERAL9 * ast ) {


    coords::REALMATRIX_LITERAL9* coords = ast2coords_->mkREALMATRIX_LITERAL9(ast, context_ ,1,2,3,4,5,6,7,8,9);

    domain::DomainObject* dom = domain_->mkDefaultDomainContainer({});
    coords2dom_->putREALMATRIX_LITERAL9(coords, dom);


    interp::REALMATRIX_LITERAL9* interp = new interp::REALMATRIX_LITERAL9(coords, dom);
    coords2interp_->putREALMATRIX_LITERAL9(coords, interp);
    interp2domain_->putREALMATRIX_LITERAL9(interp, dom); 
	this->REALMATRIX_LITERAL_vec.push_back(coords);

} 


 std::string Interpretation::toString_REALMATRIX_LITERALs(){ 
    std::vector<interp::REALMATRIX_LITERAL*> interps;
    for(auto coord : this->REALMATRIX_LITERAL_vec){
        interps.push_back(this->coords2interp_->getREALMATRIX_LITERAL(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}


std::string Interpretation::toString_Spaces() {
        int index = 0;
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
            
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
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
            
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        interps.push_back(sp);
    }
            

    return interps;
}   

std::vector<std::string> Interpretation::getSpaceNames() {
    std::vector<std::string> names;
    
	auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
    for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        names.push_back((*it)->getName());
    }
            
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
    for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        names.push_back((*it)->getName());
    }
            
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        names.push_back((*it)->getName());
    }
            

    return names;
}

std::vector<interp::Frame*> Interpretation::getFrameInterps() {
    std::vector<interp::Frame*> interps;
    
	auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
    for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            auto intfr = interp2domain_->getFrame(fr);
            interps.push_back(intfr);
        }
    }
            
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
    for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            auto intfr = interp2domain_->getFrame(fr);
            interps.push_back(intfr);
        }
    }
            
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            auto intfr = interp2domain_->getFrame(fr);
            interps.push_back(intfr);
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
            //auto intfr = interp2domain_->getFrame(fr);
            names.push_back((*it)->getName()+"."+fr->getName());
        }
    }
            
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
    for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            //auto intfr = interp2domain_->getFrame(fr);
            names.push_back((*it)->getName()+"."+fr->getName());
        }
    }
            
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            //auto intfr = interp2domain_->getFrame(fr);
            names.push_back((*it)->getName()+"."+fr->getName());
        }
    }
            

    return names;
}




    
void Interpretation::buildDefaultSpaces(){
    auto worldGeometry= domain_->mkEuclideanGeometry("geom3d","worldGeometry",3);
    auto iworldGeometry = new interp::Space(worldGeometry);
    interp2domain_->putSpace(iworldGeometry, worldGeometry);
    auto standard_frameworldGeometry = worldGeometry->getFrames()[0];
    auto interp_frameworldGeometry = new interp::Frame(standard_frameworldGeometry);
    interp2domain_->putFrame(interp_frameworldGeometry, worldGeometry->getFrames()[0]);
	auto worldTime= domain_->mkClassicalTime("time","worldTime");
    auto iworldTime = new interp::Space(worldTime);
    interp2domain_->putSpace(iworldTime, worldTime);
    auto standard_frameworldTime = worldTime->getFrames()[0];
    auto interp_frameworldTime = new interp::Frame(standard_frameworldTime);
    interp2domain_->putFrame(interp_frameworldTime, worldTime->getFrames()[0]);
	auto worldVelocity= domain_->mkClassicalVelocity("vel","worldVelocity",3);
    auto iworldVelocity = new interp::Space(worldVelocity);
    interp2domain_->putSpace(iworldVelocity, worldVelocity);
    auto standard_frameworldVelocity = worldVelocity->getFrames()[0];
    auto interp_frameworldVelocity = new interp::Frame(standard_frameworldVelocity);
    interp2domain_->putFrame(interp_frameworldVelocity, worldVelocity->getFrames()[0]);


}

void Interpretation::buildSpace(){
    int index = 0;
    int choice = 0;
    int size = 3;
    if (size == 0){
        std::cout<<"Warning: No Available Spaces to Build";
        return;
    }
    while((choice <= 0 or choice > size)){ 
        std::cout<<"Available types of Spaces to build:\n";
        std::cout <<"("<<std::to_string(++index)<<")"<<"EuclideanGeometry";
		std::cout <<"("<<std::to_string(++index)<<")"<<"ClassicalTime";
		std::cout <<"("<<std::to_string(++index)<<")"<<"ClassicalVelocity";
        std::cin>>choice;
    }
    index = 0;
    
	
	
    
}

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
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
        for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
        {
            std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
            index_to_sp[index] = *it;
        }
        int choice;
        std::cin>>choice;
        if(choice >0 and choice <=index){
            auto chosen = index_to_sp[choice];
            std::cout<<"Building Frame For : "<<chosen->toString()<<"\n";
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
            if(choice > 0 and choice<= index){
                auto parent = index_to_fr[index];
                std::cout<<"Enter Name of Frame:\n";
                std::string name;
                std::cin>>name;
                auto child = domain_->mkFrame(name, chosen, parent);
                interp::Frame* interp = new interp::Frame(child);
                interp2domain_->putFrame(interp, child);
                return;
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
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
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

}

void Interpretation::mkVarTable(){
    int idx = 0;
  

    for(auto it = this->REAL1_EXPR_vec.begin(); it != this->REAL1_EXPR_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->REAL3_EXPR_vec.begin(); it != this->REAL3_EXPR_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->REAL4_EXPR_vec.begin(); it != this->REAL4_EXPR_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->REALMATRIX_EXPR_vec.begin(); it != this->REALMATRIX_EXPR_vec.end(); it++){
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

	
    for(auto it = this->REALMATRIX_VAR_IDENT_vec.begin(); it != this->REALMATRIX_VAR_IDENT_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->REAL1_LITERAL_vec.begin(); it != this->REAL1_LITERAL_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->REAL3_LITERAL_vec.begin(); it != this->REAL3_LITERAL_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->REAL4_LITERAL_vec.begin(); it != this->REAL4_LITERAL_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }

	
    for(auto it = this->REALMATRIX_LITERAL_vec.begin(); it != this->REALMATRIX_LITERAL_vec.end(); it++){
        this->index2coords_[++idx] = *it;
        (*it)->setIndex(idx);
    }


}

//print the indexed variable table for the user
void Interpretation::printVarTable(){
  int sz = this->index2coords_.size();

  for(int i = 1; i<=sz;i++)
  {
    coords::Coords* coords = this->index2coords_[i];
    if(false){}

    else if(auto dc = dynamic_cast<coords::PAREN_REAL1_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getPAREN_REAL1_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<" Paren Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::INV_REAL1_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getINV_REAL1_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<" Inverse Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::NEG_REAL1_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getNEG_REAL1_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<"Negation Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::ADD_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getADD_REAL1_EXPR_REAL1_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<"Addition Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::SUB_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getSUB_REAL1_EXPR_REAL1_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<"Subtraction Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::MUL_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getMUL_REAL1_EXPR_REAL1_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<"Multiplication Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::DIV_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getDIV_REAL1_EXPR_REAL1_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<"Division Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REF_REAL1_VAR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREF_REAL1_VAR(dc);
        std::cout<<"Index: "<<i<<","<<"Var Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::PAREN_REAL3_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getPAREN_REAL3_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<"Paren Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::ADD_REAL3_EXPR_REAL3_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getADD_REAL3_EXPR_REAL3_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<"Addition Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::SUB_REAL3_EXPR_REAL3_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getSUB_REAL3_EXPR_REAL3_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<"Subtraction Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::INV_REAL3_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getINV_REAL3_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<" Inverse Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::NEG_REAL3_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getNEG_REAL3_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<"Negation Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::MUL_REAL3_EXPR_REAL1_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getMUL_REAL3_EXPR_REAL1_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<"Multiplication Expression,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::MUL_REALMATRIX_EXPR_REAL3_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getMUL_REALMATRIX_EXPR_REAL3_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<"Multiplication Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::DIV_REAL3_EXPR_REAL1_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getDIV_REAL3_EXPR_REAL1_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<"Division Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REF_REAL3_VAR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREF_REAL3_VAR(dc);
        std::cout<<"Index: "<<i<<","<<"Var Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::PAREN_REAL4_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getPAREN_REAL4_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<"Paren Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::ADD_REAL4_EXPR_REAL4_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getADD_REAL4_EXPR_REAL4_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<"Addition Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::MUL_REAL4_EXPR_REAL1_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getMUL_REAL4_EXPR_REAL1_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<"Multiplication Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REF_REAL4_VAR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREF_REAL4_VAR(dc);
        std::cout<<"Index: "<<i<<","<<"Var Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::PAREN_REALMATRIX_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getPAREN_REALMATRIX_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<"Paren Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<"Multiplication Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REF_EXPR_REALMATRIX_VAR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREF_EXPR_REALMATRIX_VAR(dc);
        std::cout<<"Index: "<<i<<","<<"Var Expression ,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREAL1_VAR_IDENT(dc);
        std::cout<<"Index: "<<i<<","<<"R1 Variable Identifier,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REAL3_VAR_IDENT*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREAL3_VAR_IDENT(dc);
        std::cout<<"Index: "<<i<<","<<"R3 Variable Identifier,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REAL4_VAR_IDENT*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREAL4_VAR_IDENT(dc);
        std::cout<<"Index: "<<i<<","<<"R4 Variable Identifier,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREALMATRIX_VAR_IDENT(dc);
        std::cout<<"Index: "<<i<<","<<"Matrix Variable Identifier,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REAL1_LITERAL1*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREAL1_LITERAL1(dc);
        std::cout<<"Index: "<<i<<","<<" R1 Literal From Real Value,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<"R3 Literal From 3 R1 Expressions,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REAL3_LITERAL3*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREAL3_LITERAL3(dc);
        std::cout<<"Index: "<<i<<","<<"R3 Literal From 3 Real Values,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<"R4 Literal From 4 R1 Expressions,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REAL4_LITERAL4*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREAL4_LITERAL4(dc);
        std::cout<<"Index: "<<i<<","<<" R4 Literal From 4 Real Values,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<" Matrix Literal From 3 R3 Expressions,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc);
        std::cout<<"Index: "<<i<<","<<" Matrix Literal From 9 R1 Expressions,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }

    else if(auto dc = dynamic_cast<coords::REALMATRIX_LITERAL9*>(this->index2coords_[i])){
        auto dom = (domain::DomainContainer*)this->coords2dom_->getREALMATRIX_LITERAL9(dc);
        std::cout<<"Index: "<<i<<","<<" Matrix Literal from 9 Real Values,"<<dc->toString()<<", SourceLocation:"<<dc->getSourceLoc()<<"\nExisting Interpretation: "<<dom->toString()<<std::endl;

    }
    
  }

}//make a printable, indexed table of variables that can have their types assigned by a user or oracle

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
        std::cout<<"Enter -2 to print Available Frames\n";
        std::cout<<"Enter -3 to create a New Frame\n";
        std::cout<<"Enter 0 to print the Variable Table again.\n";
        std::cout << "Enter the index of a Variable to update its physical type. Enter " << sz << " to exit and check." << std::endl;
        std::cin >> choice;
        std::cout << std::to_string(choice) << "\n";


        while ((choice == -3 || choice == -2 || choice == -1 || choice == 0 || this->index2coords_.find(choice) != this->index2coords_.end()) && choice != sz)
        {
            if (choice == -3)
            {
                this->buildFrame();
            }
            else if(choice == -2)
            {
                this->printFrames();
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

                else if(auto dc = dynamic_cast<coords::PAREN_REAL1_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getPAREN_REAL1_EXPR(dc);
                    auto interp = this->coords2interp_->getPAREN_REAL1_EXPR(dc);
                    //this->coords2dom_->erasePAREN_REAL1_EXPR(dc, dom);
                    //this->interp2domain_->erasePAREN_REAL1_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL1_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->erasePAREN_REAL1_EXPR(dc, dom);
                        //this->interp2domain_->erasePAREN_REAL1_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putPAREN_REAL1_EXPR(dc, upd_dom);
                        //this->interp2domain_->putPAREN_REAL1_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::INV_REAL1_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getINV_REAL1_EXPR(dc);
                    auto interp = this->coords2interp_->getINV_REAL1_EXPR(dc);
                    //this->coords2dom_->eraseINV_REAL1_EXPR(dc, dom);
                    //this->interp2domain_->eraseINV_REAL1_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL1_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseINV_REAL1_EXPR(dc, dom);
                        //this->interp2domain_->eraseINV_REAL1_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putINV_REAL1_EXPR(dc, upd_dom);
                        //this->interp2domain_->putINV_REAL1_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::NEG_REAL1_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getNEG_REAL1_EXPR(dc);
                    auto interp = this->coords2interp_->getNEG_REAL1_EXPR(dc);
                    //this->coords2dom_->eraseNEG_REAL1_EXPR(dc, dom);
                    //this->interp2domain_->eraseNEG_REAL1_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL1_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseNEG_REAL1_EXPR(dc, dom);
                        //this->interp2domain_->eraseNEG_REAL1_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putNEG_REAL1_EXPR(dc, upd_dom);
                        //this->interp2domain_->putNEG_REAL1_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::ADD_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getADD_REAL1_EXPR_REAL1_EXPR(dc);
                    auto interp = this->coords2interp_->getADD_REAL1_EXPR_REAL1_EXPR(dc);
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

                else if(auto dc = dynamic_cast<coords::SUB_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getSUB_REAL1_EXPR_REAL1_EXPR(dc);
                    auto interp = this->coords2interp_->getSUB_REAL1_EXPR_REAL1_EXPR(dc);
                    //this->coords2dom_->eraseSUB_REAL1_EXPR_REAL1_EXPR(dc, dom);
                    //this->interp2domain_->eraseSUB_REAL1_EXPR_REAL1_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL1_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseSUB_REAL1_EXPR_REAL1_EXPR(dc, dom);
                        //this->interp2domain_->eraseSUB_REAL1_EXPR_REAL1_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putSUB_REAL1_EXPR_REAL1_EXPR(dc, upd_dom);
                        //this->interp2domain_->putSUB_REAL1_EXPR_REAL1_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::MUL_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getMUL_REAL1_EXPR_REAL1_EXPR(dc);
                    auto interp = this->coords2interp_->getMUL_REAL1_EXPR_REAL1_EXPR(dc);
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

                else if(auto dc = dynamic_cast<coords::DIV_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getDIV_REAL1_EXPR_REAL1_EXPR(dc);
                    auto interp = this->coords2interp_->getDIV_REAL1_EXPR_REAL1_EXPR(dc);
                    //this->coords2dom_->eraseDIV_REAL1_EXPR_REAL1_EXPR(dc, dom);
                    //this->interp2domain_->eraseDIV_REAL1_EXPR_REAL1_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL1_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseDIV_REAL1_EXPR_REAL1_EXPR(dc, dom);
                        //this->interp2domain_->eraseDIV_REAL1_EXPR_REAL1_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putDIV_REAL1_EXPR_REAL1_EXPR(dc, upd_dom);
                        //this->interp2domain_->putDIV_REAL1_EXPR_REAL1_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REF_REAL1_VAR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREF_REAL1_VAR(dc);
                    auto interp = this->coords2interp_->getREF_REAL1_VAR(dc);
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

                else if(auto dc = dynamic_cast<coords::PAREN_REAL3_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getPAREN_REAL3_EXPR(dc);
                    auto interp = this->coords2interp_->getPAREN_REAL3_EXPR(dc);
                    //this->coords2dom_->erasePAREN_REAL3_EXPR(dc, dom);
                    //this->interp2domain_->erasePAREN_REAL3_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL3_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->erasePAREN_REAL3_EXPR(dc, dom);
                        //this->interp2domain_->erasePAREN_REAL3_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putPAREN_REAL3_EXPR(dc, upd_dom);
                        //this->interp2domain_->putPAREN_REAL3_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::ADD_REAL3_EXPR_REAL3_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getADD_REAL3_EXPR_REAL3_EXPR(dc);
                    auto interp = this->coords2interp_->getADD_REAL3_EXPR_REAL3_EXPR(dc);
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

                else if(auto dc = dynamic_cast<coords::SUB_REAL3_EXPR_REAL3_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getSUB_REAL3_EXPR_REAL3_EXPR(dc);
                    auto interp = this->coords2interp_->getSUB_REAL3_EXPR_REAL3_EXPR(dc);
                    //this->coords2dom_->eraseSUB_REAL3_EXPR_REAL3_EXPR(dc, dom);
                    //this->interp2domain_->eraseSUB_REAL3_EXPR_REAL3_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL3_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseSUB_REAL3_EXPR_REAL3_EXPR(dc, dom);
                        //this->interp2domain_->eraseSUB_REAL3_EXPR_REAL3_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putSUB_REAL3_EXPR_REAL3_EXPR(dc, upd_dom);
                        //this->interp2domain_->putSUB_REAL3_EXPR_REAL3_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::INV_REAL3_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getINV_REAL3_EXPR(dc);
                    auto interp = this->coords2interp_->getINV_REAL3_EXPR(dc);
                    //this->coords2dom_->eraseINV_REAL3_EXPR(dc, dom);
                    //this->interp2domain_->eraseINV_REAL3_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL3_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseINV_REAL3_EXPR(dc, dom);
                        //this->interp2domain_->eraseINV_REAL3_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putINV_REAL3_EXPR(dc, upd_dom);
                        //this->interp2domain_->putINV_REAL3_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::NEG_REAL3_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getNEG_REAL3_EXPR(dc);
                    auto interp = this->coords2interp_->getNEG_REAL3_EXPR(dc);
                    //this->coords2dom_->eraseNEG_REAL3_EXPR(dc, dom);
                    //this->interp2domain_->eraseNEG_REAL3_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL3_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseNEG_REAL3_EXPR(dc, dom);
                        //this->interp2domain_->eraseNEG_REAL3_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putNEG_REAL3_EXPR(dc, upd_dom);
                        //this->interp2domain_->putNEG_REAL3_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::MUL_REAL3_EXPR_REAL1_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getMUL_REAL3_EXPR_REAL1_EXPR(dc);
                    auto interp = this->coords2interp_->getMUL_REAL3_EXPR_REAL1_EXPR(dc);
                    //this->coords2dom_->eraseMUL_REAL3_EXPR_REAL1_EXPR(dc, dom);
                    //this->interp2domain_->eraseMUL_REAL3_EXPR_REAL1_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL3_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseMUL_REAL3_EXPR_REAL1_EXPR(dc, dom);
                        //this->interp2domain_->eraseMUL_REAL3_EXPR_REAL1_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putMUL_REAL3_EXPR_REAL1_EXPR(dc, upd_dom);
                        //this->interp2domain_->putMUL_REAL3_EXPR_REAL1_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::MUL_REALMATRIX_EXPR_REAL3_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getMUL_REALMATRIX_EXPR_REAL3_EXPR(dc);
                    auto interp = this->coords2interp_->getMUL_REALMATRIX_EXPR_REAL3_EXPR(dc);
                    //this->coords2dom_->eraseMUL_REALMATRIX_EXPR_REAL3_EXPR(dc, dom);
                    //this->interp2domain_->eraseMUL_REALMATRIX_EXPR_REAL3_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL3_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseMUL_REALMATRIX_EXPR_REAL3_EXPR(dc, dom);
                        //this->interp2domain_->eraseMUL_REALMATRIX_EXPR_REAL3_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putMUL_REALMATRIX_EXPR_REAL3_EXPR(dc, upd_dom);
                        //this->interp2domain_->putMUL_REALMATRIX_EXPR_REAL3_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::DIV_REAL3_EXPR_REAL1_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getDIV_REAL3_EXPR_REAL1_EXPR(dc);
                    auto interp = this->coords2interp_->getDIV_REAL3_EXPR_REAL1_EXPR(dc);
                    //this->coords2dom_->eraseDIV_REAL3_EXPR_REAL1_EXPR(dc, dom);
                    //this->interp2domain_->eraseDIV_REAL3_EXPR_REAL1_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL3_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseDIV_REAL3_EXPR_REAL1_EXPR(dc, dom);
                        //this->interp2domain_->eraseDIV_REAL3_EXPR_REAL1_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putDIV_REAL3_EXPR_REAL1_EXPR(dc, upd_dom);
                        //this->interp2domain_->putDIV_REAL3_EXPR_REAL1_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REF_REAL3_VAR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREF_REAL3_VAR(dc);
                    auto interp = this->coords2interp_->getREF_REAL3_VAR(dc);
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

                else if(auto dc = dynamic_cast<coords::PAREN_REAL4_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getPAREN_REAL4_EXPR(dc);
                    auto interp = this->coords2interp_->getPAREN_REAL4_EXPR(dc);
                    //this->coords2dom_->erasePAREN_REAL4_EXPR(dc, dom);
                    //this->interp2domain_->erasePAREN_REAL4_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL4_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->erasePAREN_REAL4_EXPR(dc, dom);
                        //this->interp2domain_->erasePAREN_REAL4_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putPAREN_REAL4_EXPR(dc, upd_dom);
                        //this->interp2domain_->putPAREN_REAL4_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::ADD_REAL4_EXPR_REAL4_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getADD_REAL4_EXPR_REAL4_EXPR(dc);
                    auto interp = this->coords2interp_->getADD_REAL4_EXPR_REAL4_EXPR(dc);
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

                else if(auto dc = dynamic_cast<coords::MUL_REAL4_EXPR_REAL1_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getMUL_REAL4_EXPR_REAL1_EXPR(dc);
                    auto interp = this->coords2interp_->getMUL_REAL4_EXPR_REAL1_EXPR(dc);
                    //this->coords2dom_->eraseMUL_REAL4_EXPR_REAL1_EXPR(dc, dom);
                    //this->interp2domain_->eraseMUL_REAL4_EXPR_REAL1_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL4_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseMUL_REAL4_EXPR_REAL1_EXPR(dc, dom);
                        //this->interp2domain_->eraseMUL_REAL4_EXPR_REAL1_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putMUL_REAL4_EXPR_REAL1_EXPR(dc, upd_dom);
                        //this->interp2domain_->putMUL_REAL4_EXPR_REAL1_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REF_REAL4_VAR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREF_REAL4_VAR(dc);
                    auto interp = this->coords2interp_->getREF_REAL4_VAR(dc);
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

                else if(auto dc = dynamic_cast<coords::PAREN_REALMATRIX_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getPAREN_REALMATRIX_EXPR(dc);
                    auto interp = this->coords2interp_->getPAREN_REALMATRIX_EXPR(dc);
                    //this->coords2dom_->erasePAREN_REALMATRIX_EXPR(dc, dom);
                    //this->interp2domain_->erasePAREN_REALMATRIX_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREALMATRIX_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->erasePAREN_REALMATRIX_EXPR(dc, dom);
                        //this->interp2domain_->erasePAREN_REALMATRIX_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putPAREN_REALMATRIX_EXPR(dc, upd_dom);
                        //this->interp2domain_->putPAREN_REALMATRIX_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(dc);
                    auto interp = this->coords2interp_->getMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(dc);
                    //this->coords2dom_->eraseMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(dc, dom);
                    //this->interp2domain_->eraseMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREALMATRIX_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(dc, dom);
                        //this->interp2domain_->eraseMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(dc, upd_dom);
                        //this->interp2domain_->putMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REF_EXPR_REALMATRIX_VAR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREF_EXPR_REALMATRIX_VAR(dc);
                    auto interp = this->coords2interp_->getREF_EXPR_REALMATRIX_VAR(dc);
                    //this->coords2dom_->eraseREF_EXPR_REALMATRIX_VAR(dc, dom);
                    //this->interp2domain_->eraseREF_EXPR_REALMATRIX_VAR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREALMATRIX_EXPR(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREF_EXPR_REALMATRIX_VAR(dc, dom);
                        //this->interp2domain_->eraseREF_EXPR_REALMATRIX_VAR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREF_EXPR_REALMATRIX_VAR(dc, upd_dom);
                        //this->interp2domain_->putREF_EXPR_REALMATRIX_VAR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REAL1_VAR_IDENT*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREAL1_VAR_IDENT(dc);
                    auto interp = this->coords2interp_->getREAL1_VAR_IDENT(dc);
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
                    auto interp = this->coords2interp_->getREAL3_VAR_IDENT(dc);
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
                    auto interp = this->coords2interp_->getREAL4_VAR_IDENT(dc);
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

                else if(auto dc = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREALMATRIX_VAR_IDENT(dc);
                    auto interp = this->coords2interp_->getREALMATRIX_VAR_IDENT(dc);
                    //this->coords2dom_->eraseREALMATRIX_VAR_IDENT(dc, dom);
                    //this->interp2domain_->eraseREALMATRIX_VAR_IDENT(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREALMATRIX_VAR_IDENT(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREALMATRIX_VAR_IDENT(dc, dom);
                        //this->interp2domain_->eraseREALMATRIX_VAR_IDENT(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREALMATRIX_VAR_IDENT(dc, upd_dom);
                        //this->interp2domain_->putREALMATRIX_VAR_IDENT(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REAL1_LITERAL1*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREAL1_LITERAL1(dc);
                    auto interp = this->coords2interp_->getREAL1_LITERAL1(dc);
                    //this->coords2dom_->eraseREAL1_LITERAL1(dc, dom);
                    //this->interp2domain_->eraseREAL1_LITERAL1(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL1_LITERAL(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREAL1_LITERAL1(dc, dom);
                        //this->interp2domain_->eraseREAL1_LITERAL1(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREAL1_LITERAL1(dc, upd_dom);
                        //this->interp2domain_->putREAL1_LITERAL1(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc);
                    auto interp = this->coords2interp_->getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc);
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

                else if(auto dc = dynamic_cast<coords::REAL3_LITERAL3*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREAL3_LITERAL3(dc);
                    auto interp = this->coords2interp_->getREAL3_LITERAL3(dc);
                    //this->coords2dom_->eraseREAL3_LITERAL3(dc, dom);
                    //this->interp2domain_->eraseREAL3_LITERAL3(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL3_LITERAL(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREAL3_LITERAL3(dc, dom);
                        //this->interp2domain_->eraseREAL3_LITERAL3(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREAL3_LITERAL3(dc, upd_dom);
                        //this->interp2domain_->putREAL3_LITERAL3(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc);
                    auto interp = this->coords2interp_->getREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc);
                    //this->coords2dom_->eraseREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc, dom);
                    //this->interp2domain_->eraseREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL4_LITERAL(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc, dom);
                        //this->interp2domain_->eraseREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc, upd_dom);
                        //this->interp2domain_->putREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REAL4_LITERAL4*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREAL4_LITERAL4(dc);
                    auto interp = this->coords2interp_->getREAL4_LITERAL4(dc);
                    //this->coords2dom_->eraseREAL4_LITERAL4(dc, dom);
                    //this->interp2domain_->eraseREAL4_LITERAL4(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREAL4_LITERAL(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREAL4_LITERAL4(dc, dom);
                        //this->interp2domain_->eraseREAL4_LITERAL4(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREAL4_LITERAL4(dc, upd_dom);
                        //this->interp2domain_->putREAL4_LITERAL4(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(dc);
                    auto interp = this->coords2interp_->getREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(dc);
                    //this->coords2dom_->eraseREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(dc, dom);
                    //this->interp2domain_->eraseREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREALMATRIX_LITERAL(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(dc, dom);
                        //this->interp2domain_->eraseREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(dc, upd_dom);
                        //this->interp2domain_->putREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc);
                    auto interp = this->coords2interp_->getREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc);
                    //this->coords2dom_->eraseREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc, dom);
                    //this->interp2domain_->eraseREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREALMATRIX_LITERAL(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc, dom);
                        //this->interp2domain_->eraseREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(dc, upd_dom);
                        //this->interp2domain_->putREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp, upd_dom);
                        //delete dom;
                    }
                }

                else if(auto dc = dynamic_cast<coords::REALMATRIX_LITERAL9*>(this->index2coords_[choice])){
                    auto dom = this->coords2dom_->getREALMATRIX_LITERAL9(dc);
                    auto interp = this->coords2interp_->getREALMATRIX_LITERAL9(dc);
                    //this->coords2dom_->eraseREALMATRIX_LITERAL9(dc, dom);
                    //this->interp2domain_->eraseREALMATRIX_LITERAL9(interp, dom);
                    auto upd_dom = this->oracle_->getInterpretationForREALMATRIX_LITERAL(dc, dom);
                    if(upd_dom){//remap, hopefully everything works fine from here
                        //this->coords2dom_->eraseREALMATRIX_LITERAL9(dc, dom);
                        //this->interp2domain_->eraseREALMATRIX_LITERAL9(interp, dom);
                        //upd_dom->setOperands(dom->getOperands());
                        ((domain::DomainContainer*)dom)->setValue(upd_dom);
                        //this->coords2dom_->putREALMATRIX_LITERAL9(dc, upd_dom);
                        //this->interp2domain_->putREALMATRIX_LITERAL9(interp, upd_dom);
                        //delete dom;
                    }
                }
            }
            checker_->CheckPoll();
            std::cout << "********************************************\n";
            std::cout << "********************************************\n";
            //std::cout << "********************************************\n";
            std::cout << "See type-checking output in /peirce/phys/deps/orig/PeirceOutput.lean\n";
            std::cout << "********************************************\n";
            std::cout << "********************************************\n";
            //std::cout << "********************************************\n";
            std::cout<<"Enter -1 to print Available Spaces\n";
            std::cout<<"Enter -2 to print Available Frames\n";
            std::cout<<"Enter -3 to create a New Frame\n";
            std::cout<<"Enter 0 to print the Variable Table again.\n";
            std::cout << "Enter the index of a Variable to update its physical type. Enter " << sz << " to exit and check." << std::endl;
            std::cin >> choice;
            std::cout << std::to_string(choice) << "\n";
        }
    }
    catch(std::exception ex){
        std::cout<<ex.what()<<"\n";
    }
};

void remap(coords::Coords c, domain::DomainObject newinterp){
    return;
};

