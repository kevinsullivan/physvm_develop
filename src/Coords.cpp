
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
    int begin_line_no,
    int begin_col_no,
    int end_line_no,
    int end_col_no) 
    : file_id_{file_id}, file_name_{file_name}, file_path_{file_path}, name_{name}, begin_line_no_{begin_line_no}, begin_col_no_{begin_col_no}, end_line_no_{end_line_no}, end_col_no_{end_col_no} {}

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
    retval += " End: line ";
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
std::string SEQ_GLOBALSTMT::toString() const{ return (this->getIndex() > 0 ? "INDEX"+std::to_string(this->getIndex())+".":"")+"PROGRAM" + std::string("")+ "COMMAND.B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


COMPOUND_STMT::COMPOUND_STMT(std::vector<STMT*> operands) :STMT() {
    for(auto& op : operands){
        this->operands_.push_back(op);
    }

};
std::string COMPOUND_STMT::toString() const{ return (this->getIndex() > 0 ? "INDEX"+std::to_string(this->getIndex())+".":"")+"STMT" + std::string("")+ "COMMAND.B.L"+ std::to_string(state_->begin_line_no_) + "C" + std::to_string(state_->begin_col_no_) + ".E.L" + std::to_string(state_->end_line_no_) + "C" + std::to_string(state_->end_col_no_);}


std::string VOID_FUNC_DECL_STMT::toString() const{ return (this->getIndex() > 0 ? "INDEX"+std::to_string(this->getIndex())+".":"")+"FUNC.DECL" + std::string("") + state_->name_;}
std::string MAIN_FUNC_DECL_STMT::toString() const{ return (this->getIndex() > 0 ? "INDEX"+std::to_string(this->getIndex())+".":"")+"FUNC.DECL" + std::string("") + state_->name_;}
} // namespace codecoords