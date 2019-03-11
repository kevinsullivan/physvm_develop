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

Coords::Coords(const clang::Stmt *stmt, clang::ASTContext *c) : 
    ast_type_tag_(coords::CLANG_AST_STMT), clang_stmt_(stmt), context_(c)  {
}

Coords::Coords(const clang::Decl *decl, clang::ASTContext *c) : 
    ast_type_tag_(coords::CLANG_AST_DECL), clang_decl_(decl), context_(c)  {
}

const clang::Stmt *Coords::getClangStmt() const { return clang_stmt_; }
const clang::Decl *Coords::getClangDecl() const { return clang_decl_; }

bool Coords::operator==(const Coords &other) const {
    if (ast_type_tag_ == coords::CLANG_AST_STMT) {
        return (clang_stmt_ == other.clang_stmt_);
    }
    else {  // ast_type_tag_ == coords::CLANG_AST_DECL
        return (clang_decl_ == other.clang_decl_);
    }
}

std::string Coords::toString() const {
    LOG(FATAL) << "Coords::toString. Error. Should not be called. Abstract.\n";
    return NULL;
}

std::string Coords::getSourceLoc() const {
    clang::FullSourceLoc FullLocation;
    if (ast_type_tag_ == CLANG_AST_STMT)
    {
      FullLocation = context_->getFullLoc(clang_stmt_->getBeginLoc());
    } else {
      FullLocation = context_->getFullLoc(clang_decl_->getBeginLoc());
    }
    std::string retval = "line ";
    retval += std::to_string(FullLocation.getSpellingLineNumber()); 
    retval +=  ", column ";
    retval +=  std::to_string(FullLocation.getSpellingColumnNumber());
    return retval;
}

/*************************************************************
* Coordinate subclasses, for type checking, override behaviors
*************************************************************/

/******
* Ident
******/

VecIdent::VecIdent(const clang::VarDecl *v, clang::ASTContext *c) : Coords(v, c) {}

const clang::VarDecl *VecIdent::getVarDecl() const {
    return static_cast<const clang::VarDecl*>(clang_decl_);  
}

std::string VecIdent::toString() const { 
    return getVarDecl()->getNameAsString(); 
}

/*****
* Expr
*****/


VecExpr::VecExpr(const clang::Expr *v, clang::ASTContext *c) : Coords(v, c) {}

const clang::Expr *VecExpr::getExpr() {
    return static_cast<const clang::Expr*>(clang_stmt_);  
}

std::string VecExpr::toString() const { 
    LOG(FATAL) << "Coords::VecExpr::toString. Error. Should not be called. Abstract.\n"; 
    return NULL; 
}

/*
No such intermediate node in Clang AST.
Straight to CXXConstructExpr (Vector_Lit).
Included here as stub for possible future use.
class VecLitExpr : public VecExpr {}
*/
VecVarExpr::VecVarExpr(const ast::VecVarExpr *d, clang::ASTContext *c) : VecExpr(d, c) {}

const ast::VecVarExpr *VecVarExpr::getVecVarExpr() const {
    return static_cast<const clang::DeclRefExpr*> (clang_stmt_);  
}

std::string VecVarExpr::toString() const { 
    return getVecVarExpr()->getDecl()->getNameAsString(); 
  }


VecVecAddExpr::VecVecAddExpr(
    const clang::CXXMemberCallExpr *mce, clang::ASTContext *c, coords::VecExpr *mem, coords::VecExpr *arg) 
        : VecExpr(mce, c), mem_(mem), arg_(arg) {
}

const ast::VecVecAddExpr *VecVecAddExpr::getVecVecAddExpr() {
    return static_cast<const clang::CXXMemberCallExpr*> (clang_stmt_);  
}

std::string VecVecAddExpr::toString() const {
    return "(add (" + mem_->toString() + ") (" + arg_->toString() + "))";
}


VecParenExpr::VecParenExpr(const ast::VecParenExpr *ast, clang::ASTContext *c, coords::VecExpr *expr) 
        : VecExpr(ast, c), expr_(expr) { 
}

const coords::VecExpr *VecParenExpr::getVecExpr() const { return expr_;  }

std::string VecParenExpr::toString() const {
    return "( " + expr_->toString() + ")";
}

/*******
* Values
*******/

Vector::Vector(const clang::CXXConstructExpr *vec, clang::ASTContext *c, coords::VectorCtorType tag)
      : VecExpr(vec, c), tag_(tag) {
}
  
const ast::Vector *Vector::getVector() const { 
    return static_cast<const clang::CXXConstructExpr*>(clang_stmt_); 
}

VectorCtorType Vector::getVectorType() { return tag_; }

std::string Vector::toString() const { 
    LOG(FATAL) << "Coords::Vector::toPrint: Error. Should not be called. Abstract.\n";
    return NULL;
}

Vector_Lit::Vector_Lit(const clang::CXXConstructExpr* ast, clang::ASTContext *c, ast::Scalar x, ast::Scalar y, ast::Scalar z ) 
    : Vector(ast, c, VEC_CTOR_LIT), x_(x), y_(y), z_(z) {} 
  
std::string Vector_Lit::toString() const  {
    std::string retval = "";
    retval += std::to_string(x_); 
    retval.append(" ");
    retval += std::to_string(y_); 
    retval.append(" ");
    retval += std::to_string(z_);
    return retval;
}

Vector_Var::Vector_Var(const clang::CXXConstructExpr* ast, clang::ASTContext *c, coords::VecVarExpr* expr) 
    : Vector(ast, c, VEC_CTOR_VAR), expr_(expr) { 
}

std::string Vector_Var::toString() const { 
    LOG(FATAL) << ("Vector_Var::toString() NOT YET IMPLEMENTED!\n"); 
    return NULL;
}

std::string Vector_Expr::toString() const { 
    return expr_->toString();
    //std::string("Vector_Expr::toString() STUB.\n"); 
}

Vector_Expr::Vector_Expr(const clang::CXXConstructExpr *ctor_ast, clang::ASTContext *c, 
                     coords::VecExpr* expr_coords) 
    : Vector(ctor_ast, c, VEC_CTOR_EXPR), expr_(expr_coords) {
}

/****
* Def
****/

Vector_Def::Vector_Def(const clang::DeclStmt *ast, clang::ASTContext *c, coords::VecIdent *id, coords::VecExpr *expr)
      : Coords(ast, c), id_(id), expr_(expr) {
}

coords::VecIdent *Vector_Def::getIdent() const {
    return id_;
}

coords::VecExpr *Vector_Def::getExpr() const {
    return expr_;
}

// The coup d'grace.
std::string Vector_Def::toString() const { 
    std::string retval = "def ";
    retval += id_->toString();
    retval += " := ";
    retval += expr_->toString();
    return retval;
}

} // namespace codecoords
