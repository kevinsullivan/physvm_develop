
#include "Coords.h"

#include <g3log/g3log.hpp>


namespace coords {

/*
Code coordinates provide for ontology translation, between the 
concrete types used to represent pertinent code elements in a 
given programming language and system (code language), and the 
abstract terms of a domain language. Here the code language is
Clang as used to map applications built on our simple vector
class (Vec). The domain language is one of simple vector space
expressions and objects. 
*/

// Ontology of code object types that can be coordinatized
// clang::Decl unused by Peirce, here for generalizability
//


ASTState::ASTState(
    std::string file_id,
    std::string file_name,
    std::string file_path,
    std::string name,
    int begin_line_no,
    int begin_col_no,
    int end_line_no,
    int end_col_no) 
    : file_id_{file_id}, file_name_{file_name}, file_path_{file_path}, name_{name}, begin_line_no_{begin_line_no}, begin_col_no_{begin_col_no}, end_line_no_{end_line_no}, end_col_no_{end_col_no} {}

//Coords::Coords(){
//}

bool Coords::operator==(const Coords &other) const {
    return this->state_ == other.state_;
}

std::string Coords::toString() const {
    LOG(FATAL) << "Coords::toString. Error. Should not be called. Abstract.\n";
    return NULL;
}

std::string Coords::getSourceLoc() const {
    /*clang::FullSourceLoc FullLocation;
    if (ast_type_tag_ == CLANG_AST_STMT)
    {
      FullLocation = context_->getFullLoc(clang_stmt_->getSourceRange().getEnd());
    } else {
      FullLocation = context_->getFullLoc(clang_decl_->getLocation());
    }*/
    //std::cout<<this->toString()<<std::endl;
    std::string retval = "Begin: line ";
    retval += std::to_string(this->state_->begin_line_no_);
    retval +=  ", column ";
    retval +=  std::to_string(this->state_->begin_col_no_);
    retval += " End: line ";
    retval += std::to_string(this->state_->end_line_no_);
    retval += ", column ";
    retval += std::to_string(this->state_->end_col_no_);

    return retval;
}

/*************************************************************
* Coordinate subclasses, for type checking, override behaviors
*************************************************************/


COMPOUND_STMT::COMPOUND_STMT(std::vector<STMT*> operands) :STMT() {
    for(auto& op : operands){
        this->operands_.push_back(op);
    }

};
std::string COMPOUND_STMT::toString() const{ return "Not implemented";;}


IFTHEN_EXPR_STMT::IFTHEN_EXPR_STMT(coords::EXPR *operand_1,coords::STMT *operand_2) : 
		IFCOND(),operand1(operand_1),operand2(operand_2){}
coords::EXPR* IFTHEN_EXPR_STMT::getOperand1() { return this->operand1;}
coords::STMT* IFTHEN_EXPR_STMT::getOperand2() { return this->operand2;}
std::string IFTHEN_EXPR_STMT::toString() const{ return "Not implemented";;}


IFTHENELSEIF_EXPR_STMT_IFCOND::IFTHENELSEIF_EXPR_STMT_IFCOND(coords::EXPR *operand_1,coords::STMT *operand_2,coords::IFCOND *operand_3) : 
		IFCOND(),operand1(operand_1),operand2(operand_2),operand3(operand_3){}
coords::EXPR* IFTHENELSEIF_EXPR_STMT_IFCOND::getOperand1() { return this->operand1;}
coords::STMT* IFTHENELSEIF_EXPR_STMT_IFCOND::getOperand2() { return this->operand2;}
coords::IFCOND* IFTHENELSEIF_EXPR_STMT_IFCOND::getOperand3() { return this->operand3;}
std::string IFTHENELSEIF_EXPR_STMT_IFCOND::toString() const{ return "Not implemented";;}


IFTHENELSE_EXPR_STMT_STMT::IFTHENELSE_EXPR_STMT_STMT(coords::EXPR *operand_1,coords::STMT *operand_2,coords::STMT *operand_3) : 
		IFCOND(),operand1(operand_1),operand2(operand_2),operand3(operand_3){}
coords::EXPR* IFTHENELSE_EXPR_STMT_STMT::getOperand1() { return this->operand1;}
coords::STMT* IFTHENELSE_EXPR_STMT_STMT::getOperand2() { return this->operand2;}
coords::STMT* IFTHENELSE_EXPR_STMT_STMT::getOperand3() { return this->operand3;}
std::string IFTHENELSE_EXPR_STMT_STMT::toString() const{ return "Not implemented";;}


ASSIGN_REAL1_VAR_REAL1_EXPR::ASSIGN_REAL1_VAR_REAL1_EXPR(coords::REAL1_VAR_IDENT *operand_1,coords::REAL1_EXPR *operand_2) : 
		ASSIGNMENT(),operand1(operand_1),operand2(operand_2){}
coords::REAL1_VAR_IDENT* ASSIGN_REAL1_VAR_REAL1_EXPR::getOperand1() { return this->operand1;}
coords::REAL1_EXPR* ASSIGN_REAL1_VAR_REAL1_EXPR::getOperand2() { return this->operand2;}
std::string ASSIGN_REAL1_VAR_REAL1_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


ASSIGN_REAL3_VAR_REAL3_EXPR::ASSIGN_REAL3_VAR_REAL3_EXPR(coords::REAL3_VAR_IDENT *operand_1,coords::REAL3_EXPR *operand_2) : 
		ASSIGNMENT(),operand1(operand_1),operand2(operand_2){}
coords::REAL3_VAR_IDENT* ASSIGN_REAL3_VAR_REAL3_EXPR::getOperand1() { return this->operand1;}
coords::REAL3_EXPR* ASSIGN_REAL3_VAR_REAL3_EXPR::getOperand2() { return this->operand2;}
std::string ASSIGN_REAL3_VAR_REAL3_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


ASSIGN_REAL4_VAR_REAL4_EXPR::ASSIGN_REAL4_VAR_REAL4_EXPR(coords::REAL4_VAR_IDENT *operand_1,coords::REAL4_EXPR *operand_2) : 
		ASSIGNMENT(),operand1(operand_1),operand2(operand_2){}
coords::REAL4_VAR_IDENT* ASSIGN_REAL4_VAR_REAL4_EXPR::getOperand1() { return this->operand1;}
coords::REAL4_EXPR* ASSIGN_REAL4_VAR_REAL4_EXPR::getOperand2() { return this->operand2;}
std::string ASSIGN_REAL4_VAR_REAL4_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(coords::REALMATRIX_VAR_IDENT *operand_1,coords::REALMATRIX_EXPR *operand_2) : 
		ASSIGNMENT(),operand1(operand_1),operand2(operand_2){}
coords::REALMATRIX_VAR_IDENT* ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR::getOperand1() { return this->operand1;}
coords::REALMATRIX_EXPR* ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR::getOperand2() { return this->operand2;}
std::string ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


DECL_REAL1_VAR_REAL1_EXPR::DECL_REAL1_VAR_REAL1_EXPR(coords::REAL1_VAR_IDENT *operand_1,coords::REAL1_EXPR *operand_2) : 
		DECLARE(),operand1(operand_1),operand2(operand_2){}
coords::REAL1_VAR_IDENT* DECL_REAL1_VAR_REAL1_EXPR::getOperand1() { return this->operand1;}
coords::REAL1_EXPR* DECL_REAL1_VAR_REAL1_EXPR::getOperand2() { return this->operand2;}
std::string DECL_REAL1_VAR_REAL1_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


DECL_REAL3_VAR_REAL3_EXPR::DECL_REAL3_VAR_REAL3_EXPR(coords::REAL3_VAR_IDENT *operand_1,coords::REAL3_EXPR *operand_2) : 
		DECLARE(),operand1(operand_1),operand2(operand_2){}
coords::REAL3_VAR_IDENT* DECL_REAL3_VAR_REAL3_EXPR::getOperand1() { return this->operand1;}
coords::REAL3_EXPR* DECL_REAL3_VAR_REAL3_EXPR::getOperand2() { return this->operand2;}
std::string DECL_REAL3_VAR_REAL3_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


DECL_REAL4_VAR_REAL4_EXPR::DECL_REAL4_VAR_REAL4_EXPR(coords::REAL4_VAR_IDENT *operand_1,coords::REAL4_EXPR *operand_2) : 
		DECLARE(),operand1(operand_1),operand2(operand_2){}
coords::REAL4_VAR_IDENT* DECL_REAL4_VAR_REAL4_EXPR::getOperand1() { return this->operand1;}
coords::REAL4_EXPR* DECL_REAL4_VAR_REAL4_EXPR::getOperand2() { return this->operand2;}
std::string DECL_REAL4_VAR_REAL4_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


DECL_REALMATRIX_VAR_REALMATRIX_EXPR::DECL_REALMATRIX_VAR_REALMATRIX_EXPR(coords::REALMATRIX_VAR_IDENT *operand_1,coords::REALMATRIX_EXPR *operand_2) : 
		DECLARE(),operand1(operand_1),operand2(operand_2){}
coords::REALMATRIX_VAR_IDENT* DECL_REALMATRIX_VAR_REALMATRIX_EXPR::getOperand1() { return this->operand1;}
coords::REALMATRIX_EXPR* DECL_REALMATRIX_VAR_REALMATRIX_EXPR::getOperand2() { return this->operand2;}
std::string DECL_REALMATRIX_VAR_REALMATRIX_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


DECL_REAL1_VAR::DECL_REAL1_VAR(coords::REAL1_VAR_IDENT *operand_1) : 
		DECLARE(),operand1(operand_1){}
coords::REAL1_VAR_IDENT* DECL_REAL1_VAR::getOperand1() { return this->operand1;}
std::string DECL_REAL1_VAR::toString() const{ return "Not implemented";;}


DECL_REAL3_VAR::DECL_REAL3_VAR(coords::REAL3_VAR_IDENT *operand_1) : 
		DECLARE(),operand1(operand_1){}
coords::REAL3_VAR_IDENT* DECL_REAL3_VAR::getOperand1() { return this->operand1;}
std::string DECL_REAL3_VAR::toString() const{ return "Not implemented";;}


DECL_REAL4_VAR::DECL_REAL4_VAR(coords::REAL4_VAR_IDENT *operand_1) : 
		DECLARE(),operand1(operand_1){}
coords::REAL4_VAR_IDENT* DECL_REAL4_VAR::getOperand1() { return this->operand1;}
std::string DECL_REAL4_VAR::toString() const{ return "Not implemented";;}


DECL_REALMATRIX_VAR::DECL_REALMATRIX_VAR(coords::REALMATRIX_VAR_IDENT *operand_1) : 
		DECLARE(),operand1(operand_1){}
coords::REALMATRIX_VAR_IDENT* DECL_REALMATRIX_VAR::getOperand1() { return this->operand1;}
std::string DECL_REALMATRIX_VAR::toString() const{ return "Not implemented";;}


PAREN_REAL1_EXPR::PAREN_REAL1_EXPR(coords::REAL1_EXPR *operand_1) : 
		REAL1_EXPR(),operand1(operand_1){}
coords::REAL1_EXPR* PAREN_REAL1_EXPR::getOperand1() { return this->operand1;}
std::string PAREN_REAL1_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


INV_REAL1_EXPR::INV_REAL1_EXPR(coords::REAL1_EXPR *operand_1) : 
		REAL1_EXPR(),operand1(operand_1){}
coords::REAL1_EXPR* INV_REAL1_EXPR::getOperand1() { return this->operand1;}
std::string INV_REAL1_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


NEG_REAL1_EXPR::NEG_REAL1_EXPR(coords::REAL1_EXPR *operand_1) : 
		REAL1_EXPR(),operand1(operand_1){}
coords::REAL1_EXPR* NEG_REAL1_EXPR::getOperand1() { return this->operand1;}
std::string NEG_REAL1_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


ADD_REAL1_EXPR_REAL1_EXPR::ADD_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR *operand_1,coords::REAL1_EXPR *operand_2) : 
		REAL1_EXPR(),operand1(operand_1),operand2(operand_2){}
coords::REAL1_EXPR* ADD_REAL1_EXPR_REAL1_EXPR::getOperand1() { return this->operand1;}
coords::REAL1_EXPR* ADD_REAL1_EXPR_REAL1_EXPR::getOperand2() { return this->operand2;}
std::string ADD_REAL1_EXPR_REAL1_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


SUB_REAL1_EXPR_REAL1_EXPR::SUB_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR *operand_1,coords::REAL1_EXPR *operand_2) : 
		REAL1_EXPR(),operand1(operand_1),operand2(operand_2){}
coords::REAL1_EXPR* SUB_REAL1_EXPR_REAL1_EXPR::getOperand1() { return this->operand1;}
coords::REAL1_EXPR* SUB_REAL1_EXPR_REAL1_EXPR::getOperand2() { return this->operand2;}
std::string SUB_REAL1_EXPR_REAL1_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


MUL_REAL1_EXPR_REAL1_EXPR::MUL_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR *operand_1,coords::REAL1_EXPR *operand_2) : 
		REAL1_EXPR(),operand1(operand_1),operand2(operand_2){}
coords::REAL1_EXPR* MUL_REAL1_EXPR_REAL1_EXPR::getOperand1() { return this->operand1;}
coords::REAL1_EXPR* MUL_REAL1_EXPR_REAL1_EXPR::getOperand2() { return this->operand2;}
std::string MUL_REAL1_EXPR_REAL1_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


DIV_REAL1_EXPR_REAL1_EXPR::DIV_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR *operand_1,coords::REAL1_EXPR *operand_2) : 
		REAL1_EXPR(),operand1(operand_1),operand2(operand_2){}
coords::REAL1_EXPR* DIV_REAL1_EXPR_REAL1_EXPR::getOperand1() { return this->operand1;}
coords::REAL1_EXPR* DIV_REAL1_EXPR_REAL1_EXPR::getOperand2() { return this->operand2;}
std::string DIV_REAL1_EXPR_REAL1_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


REF_REAL1_VAR::REF_REAL1_VAR(coords::REAL1_VAR_IDENT *operand_1) : 
		REAL1_EXPR(),operand1(operand_1){}
coords::REAL1_VAR_IDENT* REF_REAL1_VAR::getOperand1() { return this->operand1;}
std::string REF_REAL1_VAR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


PAREN_REAL3_EXPR::PAREN_REAL3_EXPR(coords::REAL3_EXPR *operand_1) : 
		REAL3_EXPR(),operand1(operand_1){}
coords::REAL3_EXPR* PAREN_REAL3_EXPR::getOperand1() { return this->operand1;}
std::string PAREN_REAL3_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


ADD_REAL3_EXPR_REAL3_EXPR::ADD_REAL3_EXPR_REAL3_EXPR(coords::REAL3_EXPR *operand_1,coords::REAL3_EXPR *operand_2) : 
		REAL3_EXPR(),operand1(operand_1),operand2(operand_2){}
coords::REAL3_EXPR* ADD_REAL3_EXPR_REAL3_EXPR::getOperand1() { return this->operand1;}
coords::REAL3_EXPR* ADD_REAL3_EXPR_REAL3_EXPR::getOperand2() { return this->operand2;}
std::string ADD_REAL3_EXPR_REAL3_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


SUB_REAL3_EXPR_REAL3_EXPR::SUB_REAL3_EXPR_REAL3_EXPR(coords::REAL3_EXPR *operand_1,coords::REAL3_EXPR *operand_2) : 
		REAL3_EXPR(),operand1(operand_1),operand2(operand_2){}
coords::REAL3_EXPR* SUB_REAL3_EXPR_REAL3_EXPR::getOperand1() { return this->operand1;}
coords::REAL3_EXPR* SUB_REAL3_EXPR_REAL3_EXPR::getOperand2() { return this->operand2;}
std::string SUB_REAL3_EXPR_REAL3_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


INV_REAL3_EXPR::INV_REAL3_EXPR(coords::REAL3_EXPR *operand_1) : 
		REAL3_EXPR(),operand1(operand_1){}
coords::REAL3_EXPR* INV_REAL3_EXPR::getOperand1() { return this->operand1;}
std::string INV_REAL3_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


NEG_REAL3_EXPR::NEG_REAL3_EXPR(coords::REAL3_EXPR *operand_1) : 
		REAL3_EXPR(),operand1(operand_1){}
coords::REAL3_EXPR* NEG_REAL3_EXPR::getOperand1() { return this->operand1;}
std::string NEG_REAL3_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


MUL_REAL3_EXPR_REAL1_EXPR::MUL_REAL3_EXPR_REAL1_EXPR(coords::REAL3_EXPR *operand_1,coords::REAL1_EXPR *operand_2) : 
		REAL3_EXPR(),operand1(operand_1),operand2(operand_2){}
coords::REAL3_EXPR* MUL_REAL3_EXPR_REAL1_EXPR::getOperand1() { return this->operand1;}
coords::REAL1_EXPR* MUL_REAL3_EXPR_REAL1_EXPR::getOperand2() { return this->operand2;}
std::string MUL_REAL3_EXPR_REAL1_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


MUL_REALMATRIX_EXPR_REAL3_EXPR::MUL_REALMATRIX_EXPR_REAL3_EXPR(coords::REALMATRIX_EXPR *operand_1,coords::REAL3_EXPR *operand_2) : 
		REAL3_EXPR(),operand1(operand_1),operand2(operand_2){}
coords::REALMATRIX_EXPR* MUL_REALMATRIX_EXPR_REAL3_EXPR::getOperand1() { return this->operand1;}
coords::REAL3_EXPR* MUL_REALMATRIX_EXPR_REAL3_EXPR::getOperand2() { return this->operand2;}
std::string MUL_REALMATRIX_EXPR_REAL3_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


DIV_REAL3_EXPR_REAL1_EXPR::DIV_REAL3_EXPR_REAL1_EXPR(coords::REAL3_EXPR *operand_1,coords::REAL1_EXPR *operand_2) : 
		REAL3_EXPR(),operand1(operand_1),operand2(operand_2){}
coords::REAL3_EXPR* DIV_REAL3_EXPR_REAL1_EXPR::getOperand1() { return this->operand1;}
coords::REAL1_EXPR* DIV_REAL3_EXPR_REAL1_EXPR::getOperand2() { return this->operand2;}
std::string DIV_REAL3_EXPR_REAL1_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


REF_REAL3_VAR::REF_REAL3_VAR(coords::REAL3_VAR_IDENT *operand_1) : 
		REAL3_EXPR(),operand1(operand_1){}
coords::REAL3_VAR_IDENT* REF_REAL3_VAR::getOperand1() { return this->operand1;}
std::string REF_REAL3_VAR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


PAREN_REAL4_EXPR::PAREN_REAL4_EXPR(coords::REAL4_EXPR *operand_1) : 
		REAL4_EXPR(),operand1(operand_1){}
coords::REAL4_EXPR* PAREN_REAL4_EXPR::getOperand1() { return this->operand1;}
std::string PAREN_REAL4_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


ADD_REAL4_EXPR_REAL4_EXPR::ADD_REAL4_EXPR_REAL4_EXPR(coords::REAL4_EXPR *operand_1,coords::REAL4_EXPR *operand_2) : 
		REAL4_EXPR(),operand1(operand_1),operand2(operand_2){}
coords::REAL4_EXPR* ADD_REAL4_EXPR_REAL4_EXPR::getOperand1() { return this->operand1;}
coords::REAL4_EXPR* ADD_REAL4_EXPR_REAL4_EXPR::getOperand2() { return this->operand2;}
std::string ADD_REAL4_EXPR_REAL4_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


MUL_REAL4_EXPR_REAL1_EXPR::MUL_REAL4_EXPR_REAL1_EXPR(coords::REAL4_EXPR *operand_1,coords::REAL1_EXPR *operand_2) : 
		REAL4_EXPR(),operand1(operand_1),operand2(operand_2){}
coords::REAL4_EXPR* MUL_REAL4_EXPR_REAL1_EXPR::getOperand1() { return this->operand1;}
coords::REAL1_EXPR* MUL_REAL4_EXPR_REAL1_EXPR::getOperand2() { return this->operand2;}
std::string MUL_REAL4_EXPR_REAL1_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


REF_REAL4_VAR::REF_REAL4_VAR(coords::REAL4_VAR_IDENT *operand_1) : 
		REAL4_EXPR(),operand1(operand_1){}
coords::REAL4_VAR_IDENT* REF_REAL4_VAR::getOperand1() { return this->operand1;}
std::string REF_REAL4_VAR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


PAREN_REALMATRIX_EXPR::PAREN_REALMATRIX_EXPR(coords::REALMATRIX_EXPR *operand_1) : 
		REALMATRIX_EXPR(),operand1(operand_1){}
coords::REALMATRIX_EXPR* PAREN_REALMATRIX_EXPR::getOperand1() { return this->operand1;}
std::string PAREN_REALMATRIX_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


MUL_REALMATRIX_EXPR_REALMATRIX_EXPR::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR(coords::REALMATRIX_EXPR *operand_1,coords::REALMATRIX_EXPR *operand_2) : 
		REALMATRIX_EXPR(),operand1(operand_1),operand2(operand_2){}
coords::REALMATRIX_EXPR* MUL_REALMATRIX_EXPR_REALMATRIX_EXPR::getOperand1() { return this->operand1;}
coords::REALMATRIX_EXPR* MUL_REALMATRIX_EXPR_REALMATRIX_EXPR::getOperand2() { return this->operand2;}
std::string MUL_REALMATRIX_EXPR_REALMATRIX_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


REF_EXPR_REALMATRIX_VAR::REF_EXPR_REALMATRIX_VAR(coords::REALMATRIX_VAR_IDENT *operand_1) : 
		REALMATRIX_EXPR(),operand1(operand_1){}
coords::REALMATRIX_VAR_IDENT* REF_EXPR_REALMATRIX_VAR::getOperand1() { return this->operand1;}
std::string REF_EXPR_REALMATRIX_VAR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


std::string REAL1_VAR_IDENT::toString() const{ return std::string("") + state_->name_;}
std::string REAL3_VAR_IDENT::toString() const{ return std::string("") + state_->name_;}
std::string REAL4_VAR_IDENT::toString() const{ return std::string("") + state_->name_;}
std::string REALMATRIX_VAR_IDENT::toString() const{ return std::string("") + state_->name_;}
REAL1_LITERAL1::REAL1_LITERAL1(double value_1) : 
		REAL1_LITERAL(){}
std::string REAL1_LITERAL1::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR *operand_1,coords::REAL1_EXPR *operand_2,coords::REAL1_EXPR *operand_3) : 
		REAL3_LITERAL(),operand1(operand_1),operand2(operand_2),operand3(operand_3){}
coords::REAL1_EXPR* REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand1() { return this->operand1;}
coords::REAL1_EXPR* REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand2() { return this->operand2;}
coords::REAL1_EXPR* REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand3() { return this->operand3;}
std::string REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


REAL3_LITERAL3::REAL3_LITERAL3(double value_1,double value_2,double value_3) : 
		REAL3_LITERAL(){}
std::string REAL3_LITERAL3::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR *operand_1,coords::REAL1_EXPR *operand_2,coords::REAL1_EXPR *operand_3,coords::REAL1_EXPR *operand_4) : 
		REAL4_LITERAL(),operand1(operand_1),operand2(operand_2),operand3(operand_3),operand4(operand_4){}
coords::REAL1_EXPR* REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand1() { return this->operand1;}
coords::REAL1_EXPR* REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand2() { return this->operand2;}
coords::REAL1_EXPR* REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand3() { return this->operand3;}
coords::REAL1_EXPR* REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand4() { return this->operand4;}
std::string REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


REAL4_LITERAL4::REAL4_LITERAL4(double value_1,double value_2,double value_3,double value_4) : 
		REAL4_LITERAL(){}
std::string REAL4_LITERAL4::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(coords::REAL3_EXPR *operand_1,coords::REAL3_EXPR *operand_2,coords::REAL3_EXPR *operand_3) : 
		REALMATRIX_LITERAL(),operand1(operand_1),operand2(operand_2),operand3(operand_3){}
coords::REAL3_EXPR* REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR::getOperand1() { return this->operand1;}
coords::REAL3_EXPR* REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR::getOperand2() { return this->operand2;}
coords::REAL3_EXPR* REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR::getOperand3() { return this->operand3;}
std::string REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR *operand_1,coords::REAL1_EXPR *operand_2,coords::REAL1_EXPR *operand_3,coords::REAL1_EXPR *operand_4,coords::REAL1_EXPR *operand_5,coords::REAL1_EXPR *operand_6,coords::REAL1_EXPR *operand_7,coords::REAL1_EXPR *operand_8,coords::REAL1_EXPR *operand_9) : 
		REALMATRIX_LITERAL(),operand1(operand_1),operand2(operand_2),operand3(operand_3),operand4(operand_4),operand5(operand_5),operand6(operand_6),operand7(operand_7),operand8(operand_8),operand9(operand_9){}
coords::REAL1_EXPR* REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand1() { return this->operand1;}
coords::REAL1_EXPR* REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand2() { return this->operand2;}
coords::REAL1_EXPR* REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand3() { return this->operand3;}
coords::REAL1_EXPR* REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand4() { return this->operand4;}
coords::REAL1_EXPR* REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand5() { return this->operand5;}
coords::REAL1_EXPR* REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand6() { return this->operand6;}
coords::REAL1_EXPR* REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand7() { return this->operand7;}
coords::REAL1_EXPR* REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand8() { return this->operand8;}
coords::REAL1_EXPR* REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand9() { return this->operand9;}
std::string REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


REALMATRIX_LITERAL9::REALMATRIX_LITERAL9(double value_1,double value_2,double value_3,double value_4,double value_5,double value_6,double value_7,double value_8,double value_9) : 
		REALMATRIX_LITERAL(){}
std::string REALMATRIX_LITERAL9::toString() const{ return std::string("")+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


} // namespace codecoords