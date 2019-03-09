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

Coords::Coords(const clang::Stmt *stmt) : 
    ast_type_tag_(coords::CLANG_AST_STMT), clang_stmt_(stmt)  {
}

Coords::Coords(const clang::Decl *decl) : 
    ast_type_tag_(coords::CLANG_AST_DECL), clang_decl_(decl)  {
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

// TODO: Implement proper hashing of AST nodes here
//
/*
struct CoordsHasher {
  std::size_t operator()(const Coords &k) const {
    std::size_t hash = 10101010;
    // TODO Fix hash function
    return hash;
  }
};
*/


/*************************************************************
* Coordinate subclasses, for type checking, override behaviors
*************************************************************/

/******
* Ident
******/

VecIdent::VecIdent(const clang::VarDecl *v) : Coords(v) {}

const clang::VarDecl *VecIdent::getVarDecl() const {
    return static_cast<const clang::VarDecl*>(clang_decl_);  
}

std::string VecIdent::toString() const { 
    return getVarDecl()->getNameAsString(); 
}

/*****
* Expr
*****/


// TODO: Add a dynamic type tag here
// Needed???
VecExpr::VecExpr(const clang::Expr *v) : Coords(v) {}

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

VecVarExpr::VecVarExpr(const ast::VecVarExpr *d) : VecExpr(d) {}

const ast::VecVarExpr *VecVarExpr::getVecVarExpr() const {
    return static_cast<const clang::DeclRefExpr*> (clang_stmt_);  
}

std::string VecVarExpr::toString() const { 
    return getVecVarExpr()->getDecl()->getNameAsString(); 
  }


VecVecAddExpr::VecVecAddExpr(
    const clang::CXXMemberCallExpr *mce, coords::VecExpr *mem, coords::VecExpr *arg) 
        : VecExpr(mce), mem_(mem), arg_(arg) {
}

const ast::VecVecAddExpr *VecVecAddExpr::getVecVecAddExpr() {
    return static_cast<const clang::CXXMemberCallExpr*> (clang_stmt_);  
}


std::string VecVecAddExpr::toString() const {
    return "(add (" + mem_->toString() + ") (" + arg_->toString() + "))";
}

/*******
* Values
*******/

Vector::Vector(const clang::CXXConstructExpr *vec, coords::VectorCtorType tag)
      : VecExpr(vec), tag_(tag) {
}
  
const ast::Vector *Vector::getVector() const { 
    return static_cast<const clang::CXXConstructExpr*>(clang_stmt_); 
}

VectorCtorType Vector::getVectorType() { return tag_; }

std::string Vector::toString() const { 
    LOG(FATAL) << "Coords::Vector::toPrint: Error. Should not be called. Abstract.\n";
    return NULL;
}


Vector_Lit::Vector_Lit(const clang::CXXConstructExpr* ast, ast::Scalar x, ast::Scalar y, ast::Scalar z ) 
    : Vector(ast, VEC_CTOR_LIT), x_(x), y_(y), z_(z) {} 
  
std::string Vector_Lit::toString() const  {
    std::string retval = "";
    retval += std::to_string(x_); 
    retval.append(" ");
    retval += std::to_string(y_); 
    retval.append(" ");
    retval += std::to_string(z_);
    return retval;
}

Vector_Var::Vector_Var(const clang::CXXConstructExpr* ast, coords::VecVarExpr* expr) 
    : Vector(ast, VEC_CTOR_VAR), expr_(expr) {
}

std::string Vector_Var::toString() const { 
    LOG(FATAL) << ("Vector_Var::toString() NOT YET IMPLEMENTED!\n"); 
    return NULL;
}

std::string Vector_Expr::toString() const { 
    return expr_->toString();
    //std::string("Vector_Expr::toString() STUB.\n"); 
}

Vector_Expr::Vector_Expr(const clang::CXXConstructExpr *ctor_ast, 
                     coords::VecExpr* expr_coords) 
    : Vector(ctor_ast, VEC_CTOR_EXPR), expr_(expr_coords) {
}

/*
VecVecAddExpr* Vector_Expr::getVecVecAddExpr() { 
    return expr_; 
}
*/

/****
* Def
****/

Vector_Def::Vector_Def(const clang::DeclStmt *ast, coords::VecIdent *bv, coords::VecExpr *be)
      : Coords(ast), bv_(bv), be_(be) {
}

/*const clang::DeclStmt *Vector_Def::getDeclStmt() const { 
    return static_cast<const clang::DeclStmt>stmt_; 
}*/

// TODO: Fix names of members. Change to ident_ and expr_.
//
coords::VecIdent *Vector_Def::getIdent() const {
    return bv_;
}

coords::VecExpr *Vector_Def::getExpr() const {
    return be_;
}

// The coup d'grace.
std::string Vector_Def::toString() const { 
    std::string retval = "def ";
    retval += bv_->toString();
    retval += " := ";
    retval += be_->toString();
    return retval; //"Coords::Vector_Def::toString. STUB."; 
}

} // namespace codecoords
