#include "Coords.h"

#ifndef COORDS_H
#define COORDS_H

#include "clang/AST/AST.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include <cstddef>
#include <iostream> // for cheap logging only
#include "AST.h"


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

Coords::Coords(const clang::Stmt *stmt) : ast_type(CLANG_AST_STMT) {}
Coords::Coords(const clang::Decl *decl) : ast_type(CLANG_AST_EXPR) {}

const clang::Stmt *Coords::getClangStmt() const { return clang_ast_stmt_; }
const clang::Decl *Coords::getClangDecl() const { return clang_ast_decl_; }

virtual bool Coords::operator==(const Coords &other) const {
    if (ast_type_ == CLANG_AST_STMT) {
        return (stmt_ == other.stmt_);
    }
    else {  // ast_type == CLANG_AST_DECL
        return (decl_ == other.decl_);
    }
}

virtual std::string Coords::toString() const {
    return "Coords::toString. Error. Should not be called. Abstract.\n"
}

// TODO: Implement proper hashing of AST nodes here
//
struct CoordsHasher {
  std::size_t operator()(const Coords &k) const {
    std::size_t hash = 10101010;
    // TODO Fix hash function
    return hash;
  }
};

/*************************************************************
* Coordinate subclasses, for type checking, override behaviors
*************************************************************/

/******
* Ident
******/

VecIdent::VecIdent(const clang::VarDecl v) : VecExpr(v) {}

clang::VarDecl *VecIdent::getVarDecl() {
    return static_cast<clang::VarDecl*> clang_stmt_;  
}

virtual std::string VecIdent::toString() const { 
    return getVarDecl()->getNameAsString(); 
}

/*****
* Expr
*****/


// TODO: Add a dynamic type tag here
VecExpr::VecExpr(const clang::Expr v) : Coords(v) {}

clang::Expr *VecExpr::getExpr() {
    return static_cast<clang::Expr*> clang_stmt_;  
}

virtual std::string VecExpr::toString() const { 
    return "Coords::VecExpr::toString. Error. Should not be called. Abstract.\n"; 
}

/*
No such intermediate node in Clang AST.
Straight to CXXConstructExpr (Vector_Lit).
Included here as stub for possible future use.
*/
class VecLitExpr : public VecExpr {}


VecVarExprVecVarExpr::(const clang::DeclRefExpr *d) : VecExpr(d) {}

clang::DeclRefExpr *VecVarExpr::getDeclRefExpr() {
    return static_cast<clang::DeclRefExpr*> clang_stmt_;  
}

virtual std::string VecVarExpr::toString() const { 
    return getDeclRefExpr()->getDecl()->getNameAsString(); 
  }


VecVecAddExpr::VecVecAddExpr(
    const clang::CXXMemberCallExpr *mce, 
    coords::Coords *mem, 
    coords:::Coords *arg) : VecExpr(mce) {}

clang::CXXMemberCallExpr *VecVecAddExpr::CXXMemberCallExpr() {
    return static_cast<clang::CXXMemberCallExpr*> clang_stmt_;  
}

virtual std::string VecVecAddExpr::toString() const {
    return "add (" + mem_->toString() + ") (" + arg_->toString() + ")";
}

/*******
* Values
*******/

Vector::Vector(const clang::CXXConstructExpr *vec, coords::VectorCtorType tag)
      : Coords(vec), tag_(tag) {}
  
const clang::CXXConstructExpr *Vector::getCXXConstructExpr() const { 
    return static_cast<clang::CXXConstructExpr>clang_stmt_; 
}

VectorCtorType Vector::getVectorType() { return tag_; }

virtual std::string Vector::toString() const { return "Coords::Vector::toPrint: Error. Should not be called. Abstract.\n";}


Vector_Lit::Vector_Lit(clang::CXXConstructExpr* ast, float x, float y, float z) 
    : Coords(ast), lit_(ast), tag_(VEC_CTOR_LIT), x_(x), y_(y), z_(z) {}
  
virtual std::string Vector_Lit::toString() const  { 
    return "(" + x + ", " + y + ", " + z + ")";  
}

Vector_Var::Vector_Var(lang::CXXConstructExpr* ast, const coords::VecVarExpr* expr) 
    : Coords(ast), expr_(expr), tag_(VEC_CTOR_VAR) {
}

virtual std::string Vector_Var::toString() const { 
    return "Vector_Var::toString() STUB."; 
}

Vector_Expr::Vector_Lit(const clang::CXXConstructExpr ast, coords::VecVecAddExpr* expr) 
    : Coords(ast), expr_(expr), tag_(VEC_CTOR_VAR) {
}

virtual std::string toString() const { 
    return "Vector_Expr::toString() STUB."; 
}

VecVecAddExpr* Vector_Expr::getVecVecAddExpr() { 
    return expr_; 
}

/****
* Def
****/

VectorDef::Vector_Def(const clang::DeclStmt def, coords::VecIdent *bv, coords::VecExpr *be)
      : VecExpr(declStmt), bv_(bv), be_(be) {
}

const clang::DeclStmt *VectorDef::getDeclStmt() const { 
    return static_cast<clang::DeclStmt>stmt_; 
}

coords::VecIdent *VectorDef::getIdent() const {
    get ident_;
}

coords::VecExpr *VectorDef::getExpr() const {
    get expr_;
}

virtual std::string VectorDef::toString() const { 
    return "Coords::Vector_Def::toString. STUB."; 
}

} // namespace codecoords
