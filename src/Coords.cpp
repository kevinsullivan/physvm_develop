#include "Coords.h"

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
    clang_stmt_(stmt), ast_type(CLANG_AST_STMT) {
}

Coords::Coords(const clang::Decl *decl) : 
    clang_decl_(decl), ast_type_(CLANG_AST_EXPR) {
}

const clang::Stmt *Coords::getClangStmt() const { return clang_stmt_; }
const clang::Decl *Coords::getClangDecl() const { return clang_decl_; }

bool Coords::operator==(const Coords &other) const {
    if (ast_type_ == CLANG_AST_STMT) {
        return (clang_stmt_ == other.clang_stmt_);
    }
    else {  // ast_type == CLANG_AST_DECL
        return (clang_decl_ == other.clang_decl_);
    }
}

std::string Coords::toString() const {
    return "Coords::toString. Error. Should not be called. Abstract.\n";
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

struct VecIdentHasher {
  std::size_t operator()(const VecIdent &k) const {
    std::size_t hash = 10101010;
    // TODO Fix hash function
    return hash;
  }
};

struct VecExprHasher {
  std::size_t operator()(const VecExpr &k) const {
    std::size_t hash = 10101010;
    // TODO Fix hash function
    return hash;
  }
};

struct VectorHasher {
  std::size_t operator()(const Vector &k) const {
    std::size_t hash = 10101010;
    // TODO Fix hash function
    return hash;
  }
};

struct Vector_DefHasher {
  std::size_t operator()(const Vector_Def &k) const {
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

VecIdent::VecIdent(const clang::VarDecl v) : Coords(v) {}

clang::VarDecl *VecIdent::getVarDecl() {
    return static_cast<clang::VarDecl*>(clang_decl_);  
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
    return static_cast<clang::Expr*>(clang_stmt_);  
}

std::string VecExpr::toString() const { 
    return "Coords::VecExpr::toString. Error. Should not be called. Abstract.\n"; 
}

/*
No such intermediate node in Clang AST.
Straight to CXXConstructExpr (Vector_Lit).
Included here as stub for possible future use.
class VecLitExpr : public VecExpr {}
*/

VecVarExpr::VecVarExpr(const clang::DeclRefExpr *d) : VecExpr(d) {}

const clang::DeclRefExpr *VecVarExpr::getDeclRefExpr() {
    return static_cast<clang::DeclRefExpr*> (clang_stmt_);  
}

std::string VecVarExpr::toString() const { 
    return getDeclRefExpr()->getDecl()->getNameAsString(); 
  }


VecVecAddExpr::VecVecAddExpr(
    const clang::CXXMemberCallExpr *mce, 
    coords::Coords *mem, 
    coords:::Coords *arg) : VecExpr(mce) {
std::cerr << "VecVecAddExpr::VecVecAddExpr. Warn. Empty implementation.\n";
}

clang::CXXMemberCallExpr *VecVecAddExpr::getCXXMemberCallExpr() {
    return static_cast<clang::CXXMemberCallExpr*> (clang_stmt_);  
}


std::string VecVecAddExpr::toString() const {
    return "add (" + mem_->toString() + ") (" + arg_->toString() + ")";
}

/*******
* Values
*******/

Vector::Vector(const clang::CXXConstructExpr *vec, coords::VectorCtorType tag)
      : VecExpr(vec), tag_(tag) {
}
  
const clang::CXXConstructExpr *Vector::getCXXConstructExpr() const { 
    return static_cast<clang::CXXConstructExpr>(clang_stmt_); 
}

VectorCtorType Vector::getVectorType() { return tag_; }

virtual std::string Vector::toString() const { return "Coords::Vector::toPrint: Error. Should not be called. Abstract.\n";}


Vector_Lit::Vector_Lit(clang::CXXConstructExpr* ast, ast::Scalar a) 
    : Vector(ast, VEC_CTOR_LIT), lit_(ast), a_(a) {}
  
std::string Vector_Lit::toString() const  { 
    return "( 0 : Stub)";  
}

Vector_Var::Vector_Var(const clang::CXXConstructExpr* ast, coords::VecVarExpr* expr) 
    : Vector(ast, VEC_CTOR_VAR), expr_(expr) {
}

std::string Vector_Var::toString()  { 
    return "Vector_Var::toString() STUB."; 
}

std::string Vector_Expr::toString()  { 
    return "Vector_Expr::toString() STUB."; 
}

Vector_Expr::Vector_Expr(const clang::CXXConstructExpr ast, 
                     coords::VecExpr* expr) 
    : Vector(ast, VEC_CTOR_EXPR), expr_(expr) {
}

/*
VecVecAddExpr* Vector_Expr::getVecVecAddExpr() { 
    return expr_; 
}
*/

/****
* Def
****/

Vector_Def::Vector_Def(const clang::DeclStmt def, coords::VecIdent *bv, coords::VecExpr *be)
      : VecExpr(declStmt), bv_(bv), be_(be) {
}

/*const clang::DeclStmt *Vector_Def::getDeclStmt() const { 
    return static_cast<clang::DeclStmt>stmt_; 
}*/

coords::VecIdent *Vector_Def::getIdent() const {
    return ident_;
}

coords::VecExpr *Vector_Def::getExpr() const {
    return expr_;
}

std::string Vector_Def::toString() const { 
    return "Coords::Vector_Def::toString. STUB."; 
}

} // namespace codecoords
