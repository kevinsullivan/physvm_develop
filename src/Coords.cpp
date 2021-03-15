
#include "Coords.h"

#include <g3log/g3log.hpp>
#include <memory>


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
    std::string code,
    int begin_line_no,
    int begin_col_no,
    int end_line_no,
    int end_col_no) 
    : file_id_{file_id}, file_name_{file_name}, file_path_{file_path}, name_{name}, code_{code}, begin_line_no_{begin_line_no}, begin_col_no_{begin_col_no}, end_line_no_{end_line_no}, end_col_no_{end_col_no} {}

//Coords::Coords(){
//}

void Coords::setIndex(int index){
    this->index_ = index;
}

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
    retval += "\tEnd: line ";
    retval += std::to_string(this->state_->end_line_no_);
    retval += ", column ";
    retval += std::to_string(this->state_->end_col_no_);

    return retval;
}

/*************************************************************
* Coordinate subclasses, for type checking, override behaviors
*************************************************************/


SEQ_GLOBALSTMT::SEQ_GLOBALSTMT(std::vector<GLOBALSTMT*> operands) :PROGRAM() {
    for(auto& op : operands){
        this->operands_.push_back(op);
    }

};
std::string SEQ_GLOBALSTMT::toString() const{ return (this->getIndex() > 0 ? "INDEX" + std::to_string(this->getIndex()) + ".":"")+"PROGRAM" + std::string("");}


COMPOUND_STMT::COMPOUND_STMT(std::vector<STMT*> operands) :STMT() {
    for(auto& op : operands){
        this->operands_.push_back(op);
    }

};
std::string COMPOUND_STMT::toString() const{ return (this->getIndex() > 0 ? "INDEX" + std::to_string(this->getIndex()) + ".":"")+"STMT" + std::string("");}


std::string VOID_FUNC_DECL_STMT::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}
std::string MAIN_FUNC_DECL_STMT::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}
DECL_REAL1_VAR_REAL1_EXPR::DECL_REAL1_VAR_REAL1_EXPR(coords::REAL1_VAR_IDENT *operand_1,coords::REAL1_EXPR *operand_2) : 
		DECLARE(),operand1(operand_1),operand2(operand_2){}
coords::REAL1_VAR_IDENT* DECL_REAL1_VAR_REAL1_EXPR::getOperand1() { return this->operand1;}
coords::REAL1_EXPR* DECL_REAL1_VAR_REAL1_EXPR::getOperand2() { return this->operand2;}
std::string DECL_REAL1_VAR_REAL1_EXPR::toString() const{ return operand1->toString();}


DECL_REAL3_VAR_REAL3_EXPR::DECL_REAL3_VAR_REAL3_EXPR(coords::REAL3_VAR_IDENT *operand_1,coords::REAL3_EXPR *operand_2) : 
		DECLARE(),operand1(operand_1),operand2(operand_2){}
coords::REAL3_VAR_IDENT* DECL_REAL3_VAR_REAL3_EXPR::getOperand1() { return this->operand1;}
coords::REAL3_EXPR* DECL_REAL3_VAR_REAL3_EXPR::getOperand2() { return this->operand2;}
std::string DECL_REAL3_VAR_REAL3_EXPR::toString() const{ return operand1->toString();}


DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords::REALMATRIX4_VAR_IDENT *operand_1,coords::REALMATRIX4_EXPR *operand_2) : 
		DECLARE(),operand1(operand_1),operand2(operand_2){}
coords::REALMATRIX4_VAR_IDENT* DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR::getOperand1() { return this->operand1;}
coords::REALMATRIX4_EXPR* DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR::getOperand2() { return this->operand2;}
std::string DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR::toString() const{ return operand1->toString();}


DECL_REAL4_VAR_REAL4_EXPR::DECL_REAL4_VAR_REAL4_EXPR(coords::REAL4_VAR_IDENT *operand_1,coords::REAL4_EXPR *operand_2) : 
		DECLARE(),operand1(operand_1),operand2(operand_2){}
coords::REAL4_VAR_IDENT* DECL_REAL4_VAR_REAL4_EXPR::getOperand1() { return this->operand1;}
coords::REAL4_EXPR* DECL_REAL4_VAR_REAL4_EXPR::getOperand2() { return this->operand2;}
std::string DECL_REAL4_VAR_REAL4_EXPR::toString() const{ return operand1->toString();}


DECL_REAL1_VAR::DECL_REAL1_VAR(coords::REAL1_VAR_IDENT *operand_1) : 
		DECLARE(),operand1(operand_1){}
coords::REAL1_VAR_IDENT* DECL_REAL1_VAR::getOperand1() { return this->operand1;}
std::string DECL_REAL1_VAR::toString() const{ return operand1->toString();}


DECL_REAL3_VAR::DECL_REAL3_VAR(coords::REAL3_VAR_IDENT *operand_1) : 
		DECLARE(),operand1(operand_1){}
coords::REAL3_VAR_IDENT* DECL_REAL3_VAR::getOperand1() { return this->operand1;}
std::string DECL_REAL3_VAR::toString() const{ return operand1->toString();}


DECL_REALMATRIX4_VAR::DECL_REALMATRIX4_VAR(coords::REALMATRIX4_VAR_IDENT *operand_1) : 
		DECLARE(),operand1(operand_1){}
coords::REALMATRIX4_VAR_IDENT* DECL_REALMATRIX4_VAR::getOperand1() { return this->operand1;}
std::string DECL_REALMATRIX4_VAR::toString() const{ return operand1->toString();}


DECL_REAL4_VAR::DECL_REAL4_VAR(coords::REAL4_VAR_IDENT *operand_1) : 
		DECLARE(),operand1(operand_1){}
coords::REAL4_VAR_IDENT* DECL_REAL4_VAR::getOperand1() { return this->operand1;}
std::string DECL_REAL4_VAR::toString() const{ return operand1->toString();}


REF_REALMATRIX4_VAR::REF_REALMATRIX4_VAR(coords::REALMATRIX4_VAR_IDENT *operand_1) : 
		REALMATRIX4_EXPR(),operand1(operand_1){}
coords::REALMATRIX4_VAR_IDENT* REF_REALMATRIX4_VAR::getOperand1() { return this->operand1;}
std::string REF_REALMATRIX4_VAR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(coords::REALMATRIX4_EXPR *operand_1,coords::REALMATRIX4_EXPR *operand_2) : 
		REALMATRIX4_EXPR(),operand1(operand_1),operand2(operand_2){}
coords::REALMATRIX4_EXPR* MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR::getOperand1() { return this->operand1;}
coords::REALMATRIX4_EXPR* MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR::getOperand2() { return this->operand2;}
std::string MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


REF_REAL4_VAR::REF_REAL4_VAR(coords::REAL4_VAR_IDENT *operand_1,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2,std::shared_ptr<float> value3) : 
		REAL4_EXPR( value0, value1, value2, value3),operand1(operand_1){}
coords::REAL4_VAR_IDENT* REF_REAL4_VAR::getOperand1() { return this->operand1;}
std::string REF_REAL4_VAR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


ADD_REAL4_EXPR_REAL4_EXPR::ADD_REAL4_EXPR_REAL4_EXPR(coords::REAL4_EXPR *operand_1,coords::REAL4_EXPR *operand_2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2,std::shared_ptr<float> value3) : 
		REAL4_EXPR( value0, value1, value2, value3),operand1(operand_1),operand2(operand_2){}
coords::REAL4_EXPR* ADD_REAL4_EXPR_REAL4_EXPR::getOperand1() { return this->operand1;}
coords::REAL4_EXPR* ADD_REAL4_EXPR_REAL4_EXPR::getOperand2() { return this->operand2;}
std::string ADD_REAL4_EXPR_REAL4_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


MUL_REAL4_EXPR_REAL4_EXPR::MUL_REAL4_EXPR_REAL4_EXPR(coords::REAL4_EXPR *operand_1,coords::REAL4_EXPR *operand_2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2,std::shared_ptr<float> value3) : 
		REAL4_EXPR( value0, value1, value2, value3),operand1(operand_1),operand2(operand_2){}
coords::REAL4_EXPR* MUL_REAL4_EXPR_REAL4_EXPR::getOperand1() { return this->operand1;}
coords::REAL4_EXPR* MUL_REAL4_EXPR_REAL4_EXPR::getOperand2() { return this->operand2;}
std::string MUL_REAL4_EXPR_REAL4_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


REF_REAL3_VAR::REF_REAL3_VAR(coords::REAL3_VAR_IDENT *operand_1,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) : 
		REAL3_EXPR( value0, value1, value2),operand1(operand_1){}
coords::REAL3_VAR_IDENT* REF_REAL3_VAR::getOperand1() { return this->operand1;}
std::string REF_REAL3_VAR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


ADD_REAL3_EXPR_REAL3_EXPR::ADD_REAL3_EXPR_REAL3_EXPR(coords::REAL3_EXPR *operand_1,coords::REAL3_EXPR *operand_2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) : 
		REAL3_EXPR( value0, value1, value2),operand1(operand_1),operand2(operand_2){}
coords::REAL3_EXPR* ADD_REAL3_EXPR_REAL3_EXPR::getOperand1() { return this->operand1;}
coords::REAL3_EXPR* ADD_REAL3_EXPR_REAL3_EXPR::getOperand2() { return this->operand2;}
std::string ADD_REAL3_EXPR_REAL3_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


LMUL_REAL1_EXPR_REAL3_EXPR::LMUL_REAL1_EXPR_REAL3_EXPR(coords::REAL1_EXPR *operand_1,coords::REAL3_EXPR *operand_2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) : 
		REAL3_EXPR( value0, value1, value2),operand1(operand_1),operand2(operand_2){}
coords::REAL1_EXPR* LMUL_REAL1_EXPR_REAL3_EXPR::getOperand1() { return this->operand1;}
coords::REAL3_EXPR* LMUL_REAL1_EXPR_REAL3_EXPR::getOperand2() { return this->operand2;}
std::string LMUL_REAL1_EXPR_REAL3_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


RMUL_REAL3_EXPR_REAL1_EXPR::RMUL_REAL3_EXPR_REAL1_EXPR(coords::REAL3_EXPR *operand_1,coords::REAL1_EXPR *operand_2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) : 
		REAL3_EXPR( value0, value1, value2),operand1(operand_1),operand2(operand_2){}
coords::REAL3_EXPR* RMUL_REAL3_EXPR_REAL1_EXPR::getOperand1() { return this->operand1;}
coords::REAL1_EXPR* RMUL_REAL3_EXPR_REAL1_EXPR::getOperand2() { return this->operand2;}
std::string RMUL_REAL3_EXPR_REAL1_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


TMUL_REALMATRIX4_EXPR_REAL3_EXPR::TMUL_REALMATRIX4_EXPR_REAL3_EXPR(coords::REALMATRIX4_EXPR *operand_1,coords::REAL3_EXPR *operand_2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) : 
		REAL3_EXPR( value0, value1, value2),operand1(operand_1),operand2(operand_2){}
coords::REALMATRIX4_EXPR* TMUL_REALMATRIX4_EXPR_REAL3_EXPR::getOperand1() { return this->operand1;}
coords::REAL3_EXPR* TMUL_REALMATRIX4_EXPR_REAL3_EXPR::getOperand2() { return this->operand2;}
std::string TMUL_REALMATRIX4_EXPR_REAL3_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


LREF_REAL3_VAR::LREF_REAL3_VAR(coords::REAL3_VAR_IDENT *operand_1,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) : 
		REAL3_LEXPR( value0, value1, value2),operand1(operand_1){}
coords::REAL3_VAR_IDENT* LREF_REAL3_VAR::getOperand1() { return this->operand1;}
std::string LREF_REAL3_VAR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


REF_REAL1_VAR::REF_REAL1_VAR(coords::REAL1_VAR_IDENT *operand_1,std::shared_ptr<float> value0) : 
		REAL1_EXPR( value0),operand1(operand_1){}
coords::REAL1_VAR_IDENT* REF_REAL1_VAR::getOperand1() { return this->operand1;}
std::string REF_REAL1_VAR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


ADD_REAL1_EXPR_REAL1_EXPR::ADD_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR *operand_1,coords::REAL1_EXPR *operand_2,std::shared_ptr<float> value0) : 
		REAL1_EXPR( value0),operand1(operand_1),operand2(operand_2){}
coords::REAL1_EXPR* ADD_REAL1_EXPR_REAL1_EXPR::getOperand1() { return this->operand1;}
coords::REAL1_EXPR* ADD_REAL1_EXPR_REAL1_EXPR::getOperand2() { return this->operand2;}
std::string ADD_REAL1_EXPR_REAL1_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


MUL_REAL1_EXPR_REAL1_EXPR::MUL_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR *operand_1,coords::REAL1_EXPR *operand_2,std::shared_ptr<float> value0) : 
		REAL1_EXPR( value0),operand1(operand_1),operand2(operand_2){}
coords::REAL1_EXPR* MUL_REAL1_EXPR_REAL1_EXPR::getOperand1() { return this->operand1;}
coords::REAL1_EXPR* MUL_REAL1_EXPR_REAL1_EXPR::getOperand2() { return this->operand2;}
std::string MUL_REAL1_EXPR_REAL1_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


std::string REAL1_VAR_IDENT::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}
std::string REAL3_VAR_IDENT::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}
std::string REAL4_VAR_IDENT::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}
std::string REALMATRIX4_VAR_IDENT::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}
REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR *operand_1,coords::REAL1_EXPR *operand_2,coords::REAL1_EXPR *operand_3,coords::REAL1_EXPR *operand_4,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2,std::shared_ptr<float> value3) : 
		REAL4_LITERAL( value0, value1, value2, value3),operand1(operand_1),operand2(operand_2),operand3(operand_3),operand4(operand_4){}
coords::REAL1_EXPR* REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand1() { return this->operand1;}
coords::REAL1_EXPR* REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand2() { return this->operand2;}
coords::REAL1_EXPR* REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand3() { return this->operand3;}
coords::REAL1_EXPR* REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand4() { return this->operand4;}
std::string REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


REAL4_EMPTY::REAL4_EMPTY(std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2,std::shared_ptr<float> value3) : 
		REAL4_LITERAL( value0, value1, value2, value3){}
std::string REAL4_EMPTY::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR *operand_1,coords::REAL1_EXPR *operand_2,coords::REAL1_EXPR *operand_3,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) : 
		REAL3_LITERAL( value0, value1, value2),operand1(operand_1),operand2(operand_2),operand3(operand_3){}
coords::REAL1_EXPR* REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand1() { return this->operand1;}
coords::REAL1_EXPR* REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand2() { return this->operand2;}
coords::REAL1_EXPR* REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::getOperand3() { return this->operand3;}
std::string REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


REAL3_EMPTY::REAL3_EMPTY(std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) : 
		REAL3_LITERAL( value0, value1, value2){}
std::string REAL3_EMPTY::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


REAL1_LIT::REAL1_LIT(std::shared_ptr<float> value0) : 
		REAL1_LITERAL( value0){}
std::string REAL1_LIT::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


REALMATRIX4_EMPTY::REALMATRIX4_EMPTY() : 
		REALMATRIX4_LITERAL(){}
std::string REALMATRIX4_EMPTY::toString() const{ return std::string("") + state_->name_+ ".B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


} // namespace codecoords