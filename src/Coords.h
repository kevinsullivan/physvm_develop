#ifndef COORDS_H
#define COORDS_H

#include "clang/AST/AST.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include <cstddef>
#include <iostream> // for cheap logging only
#include "AST.h"


/*
Code coordinates provide for ontology translation, between the 
concrete types used to represent pertinent code elements in a 
given programming language and system (code language), and the 
abstract terms of a domain language. Here the code language is
Clang as used to map applications built on our simple vector
class (Vec). The domain language is one of simple vector space
expressions and objects. 
*/

//using namespace clang;
//using namespace clang::ast_matchers;
//using namespace std;

namespace coords {

// Ontology of code object types that can be coordinatized
// clang::Decl unused by Peirce, here for generalizability
//
enum ast_type { CLANG_AST_STMT, CLANG_AST_DECL };

class Coords {
public:

  Coords(const clang::Stmt *stmt);
  Coords(const clang::Decl *decl); 

  // Note: Clang architecture showing through here. Clang AST base types. 
  const clang::Stmt *getClangStmt() const { return clang_ast_stmt_; }
  const clang::Decl *getClangDecl() const { return clang_ast_decl_(); }

  virtual bool operator==(const Coords &other) const;
  virtual std::string toString() const;

  private:
    clang_ast_type tag_;
    clang::Stmt *clang_ast_stmt_;
    clang::Decl *clang_ast_decl_;
  }

private:
  ast_type ast_type_;
  const clang::Stmt *clang_stmt_;
  const clang::Decl *clang_decl_;
};

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

class VecIdent : public VecExpr {
public:
  VecIdent(const clang::VarDecl v) : VecExpr(v) {}
  clang::VarDecl *getVarDecl() {
    return static_cast<clang::VarDecl*> clang_stmt_;  
  }
  virtual std::string toString() const { 
    return getVarDecl()->getNameAsString(); 
  }
};

/*****
* Expr
*****/


// TODO: Add a dynamic type tag here
class VecExpr : public Coords {
public:
  VecExpr(const clang::Expr v) : Coords(v) {}
  clang::Expr *getExpr() {
    return static_cast<clang::Expr*> clang_stmt_;  
  }
  virtual std::string toString() const { 
    return "Coords::VecExpr::toString. Error. Should not be called. Abstract.\n"; 
  }
};

/*
class VecLitExpr : public VecExpr {
public:
  VecLitExpr(const clang::CXXConstructExpr*) 
    : Coords(v) {}
  clang::CXXConstructExpr *getCXXConstructExpr() { 
    return static_cast<clang::CXXConstructExpr*> clang_stmt_;
  }
  virtual std::string toString() const { 
    return "(mk_vector 0)"; 
  }
};
*/

class VecVarExpr : public VecExpr {
public:
  VecVarExpr(const clang::DeclRefExpr *d) : VecExpr(d) {}
  clang::DeclRefExpr *getDeclRefExpr() {
    return static_cast<clang::DeclRefExpr*> clang_stmt_;  
  }
  virtual std::string toString() const { 
    return getDeclRefExpr()->getDecl()->getNameAsString(); 
  }
};

class VecVecAddExpr : public VecExpr {
public:
  VecVecAddExpr(const clang::CXXMemberCallExpr *mce, coords::Coords *mem, coords:::Coords *arg) : VecExpr(mce) {}
  clang::CXXMemberCallExpr *CXXMemberCallExpr() {
    return static_cast<clang::CXXMemberCallExpr*> clang_stmt_;  
  }
  // TODO: add accessors for left and right?
  virtual std::string toString() const {
    return "add (" + mem_->toString() + ") (" + arg_->toString() + ")";
private:
  const coords::Coords *mem_;
  const coords::Coords *arg_;

};

enum VectorCtorType { VEC_CTOR_LIT, VEC_CTOR_EXPR, VEC_CTOR_VAR };

class Vector : Coords {
public:
  Vector(const clang::CXXConstructExpr *vec, coords::VectorCtorType tag)
      : Coords(vec), tag_(tag) {}
  const clang::CXXConstructExpr *getCXXConstructExpr() const { 
    return static_cast<clang::CXXConstructExpr>clang_stmt_; 
  }
  VectorCtorType getVectorType() { return tag_; }
  virtual std::string toString() const { return "Coords::Vector::toPrint: Error. Should not be called. Abstract.\n";}

protected:
    const VectorCtorType tag_;
};

class Vector_Lit : public Vector {
public:
  Vector_Lit(clang::CXXConstructExpr* ast) 
    : Coords(ast), lit_(ast), tag_(VEC_CTOR_LIT), x_(0), y_(0), z_(0) {}
  // TODO: methods to get x, y, z
  virtual std::string toString() const { return "Vector_Lit::toString() STUB."; }
private:
  float x_;
  float y_;
  float z_;
};

class Vector_Var : public Vector {
public:
  Vector_Lit(lang::CXXConstructExpr* ast, const coords::VecVarExpr* expr) : Coords(ast), expr_(expr), tag_(VEC_CTOR_VAR) {}
  virtual std::string toString() const { return "Vector_Var::toString() STUB."; }
  VecVarExpr*  getVecVarExpr() { return expr_; }
private:
  VecVarExpr* expr_;
};

// change name to VecVecAddExpr? Or generalize from that a bit.
class Vector_Expr : public Vector {
public:
  Vector_Lit(const clang::CXXConstructExpr ast, coords::VecVecAddExpr* expr) : Coords(ast), expr_(expr), tag_(VEC_CTOR_VAR) {}
  virtual std::string toString() const { return "Vector_Expr::toString() STUB."; }
  VecVecAddExpr* getVecVecAddExpr() { return expr_; }
private:
  VecVecAddExpr* expr_;
};


/****
* Def
****/

class VectorDef : public Coords {
public:
  VecDef(const clang::DeclStmt def, coords::VecIdent *bv, coords::VecExpr *be)
      : VecExpr(declStmt), bv_(bv), be_(be),  {}
  const clang::DeclStmt *getDeclStmt() const { 
    return static_cast<clang::DeclStmt>stmt_; 
  }
  // TODO: Maybe drop the consts?
  coords::VecIdent *getIdent() const;
  coords::VecExpr *getExpr() const;
  virtual std::string toString() const { return "Coords::VecDef::toString. STUB."; }
private:
  VecIdent *bv_;
  VecExpr *be_;
};

} // namespace codecoords


#endif