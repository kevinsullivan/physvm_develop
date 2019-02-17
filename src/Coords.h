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
  const clang::Stmt *getClangStmt() const;
  const clang::Decl *getClangDecl() const;

  virtual bool operator==(const Coords &other) const;
  virtual std::string toString() const;

  private:
    // TODO: Make it a tagged union to save some space
    ast_type tag_;
    clang::Stmt *clang_ast_stmt_;
    clang::Decl *clang_ast_decl_;

private:
  ast_type ast_type_;
  const clang::Stmt *clang_stmt_;
  const clang::Decl *clang_decl_;
};

struct CoordsHasher; 

/*************************************************************
* Coordinate subclasses, for type checking, override behaviors
*************************************************************/

/******
* Ident
******/

class VecIdent : public Coords {
public:
  VecIdent(const clang::VarDecl *v);
  clang::VarDecl *getVarDecl();
  virtual std::string toString() const;
};

/*****
* Expr
*****/


// TODO: Add a dynamic type tag here
class VecExpr : public Coords {
public:
  VecExpr(const clang::Expr v);
  clang::Expr *getExpr();
  virtual std::string toString() const;
};

/* 
No such intermediate node in Clang AST.
Goes straight to CXXConstructExpr. Use
Vector_Lit.
*/
class VecLitExpr : public Coords {};


class VecVarExpr : public VecExpr {
public:
  VecVarExpr(const clang::DeclRefExpr *d);
  clang::DeclRefExpr *getDeclRefExpr();
  virtual std::string toString() const;
private:
  coords::Coords *var_; // TODO: Fix
};

  // TODO: add accessors for left and right?
class VecVecAddExpr : public VecExpr {
public:
  VecVecAddExpr(const clang::CXXMemberCallExpr *mce, coords::Coords *mem, coords::Coords *arg);
  clang::CXXMemberCallExpr *CXXMemberCallExpr();
  virtual std::string toString() const;
private:
  coords::Coords *mem_;
  coords::Coords *arg_;

};

enum VectorCtorType { VEC_CTOR_LIT, VEC_CTOR_EXPR, VEC_CTOR_VAR };

class Vector : Coords {
public:
  Vector(const clang::CXXConstructExpr *vec, coords::VectorCtorType tag);
  const clang::CXXConstructExpr *getCXXConstructExpr() const;
  VectorCtorType getVectorType();
  virtual std::string toString() const;
protected:
    const VectorCtorType tag_;
};

// TODO: methods to get x, y, z
class Vector_Lit : public Vector {
public:
  Vector_Lit(clang::CXXConstructExpr* ast, float x, float y, float z);
  virtual std::string toString() const;
private:
  float x_;
  float y_;
  float z_;
};

class Vector_Var : public Vector {
public:
  Vector_Var(clang::CXXConstructExpr* ast, const coords::VecVarExpr* expr);
  virtual std::string toString() const;
  VecVarExpr*  getVecVarExpr();
private:
  VecVarExpr* expr_;
};

// change name to VecVecAddExpr? Or generalize from that a bit.
class Vector_Expr : public Vector {
public:
  Vector_Expr(const clang::CXXConstructExpr ast, coords::Vector_Expr* expr);
  virtual std::string toString() const;
  Vector_Expr* getVector_Expr();
private:
  Vector_Expr* expr_;
};


/****
* Def
****/

class Vector_Def : public Coords {
public:
  Vector_Def(const clang::DeclStmt def, coords::VecIdent *bv, coords::VecExpr *be);
  const clang::DeclStmt *getDeclStmt() const;
  coords::VecIdent *getIdent() const;
  coords::VecExpr *getExpr() const;
  virtual std::string toString() const;
  private:
  VecIdent *bv_;
  VecExpr *be_;
};

} // namespace codecoords


#endif