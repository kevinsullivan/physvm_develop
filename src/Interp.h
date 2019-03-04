#ifndef INTERP_H
#define INTERP_H

#include "clang/AST/AST.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include <cstddef>
#include <iostream> // for cheap logging only

#include "Coords.h"
#include "AST.h"
#include "Domain.h"

namespace interp {

class VecIdent;
class VecExpr;
class VecVarExpr;
class VecVecAddExpr;
class Vector;
class Vector_Lit;
class Vector_Var;
class Vector_Expr;
class Vector_Def;

enum domType {
    dom_vecIdent_type, 
    dom_vecExpr_type, 
    dom_vector_type, 
    dom_vector_def_type
};

class Interp {
public:
  Interp(coords::Coords c, domain::VecIdent *d);
  Interp(coords::Coords c, domain::VecExpr *d);
  Interp(coords::Coords c, domain::Vector *d);
  Interp(coords::Coords c, domain::Vector_Def *d);
  virtual std::string toString();
private:
  coords::Coords *coords_;
  domType type_;
  // TODO: make it a union
  domain::VecIdent * ident_;
  domain::VecExpr* expr_;
	domain::Vector* vector_;
	domain::Vector_Def* def_;
};

/*************************************************************
 * Coordinate subclasses, for type checking, override behaviors
 *************************************************************/

/******
 * Ident
 ******/


/***
**** TODO: Change types in all methods to ast:: abstractions.
***/

class VecIdent : public Interp {
public:
  VecIdent(coords::VecIdent* c, domain::VecIdent* d);
  const clang::VarDecl *getVarDecl() const;
  virtual std::string toString() const;
  bool operator==(const VecIdent &other) const {
    return (clang_decl_ == other.clang_decl_);
  }
};


/*****
 * Expr
 *****/

// TODO: Add a dynamic type tag here
// Abstract
class VecExpr : public Interp {
public:
  VecExpr(coords::VecExpr*, domain::VecExpr*);
  const ast::VecExpr *getExpr();
  virtual std::string toString() const;
  bool operator==(const VecExpr &other) const {
    return (clang_stmt_ == other.clang_stmt_);
  }
};


class VecVarExpr : public VecExpr {
public:
  VecVarExpr(coords::VecVarExpr*, domain::VecVarExpr*);
  const ast::VecVarExpr *getVecVarExpr() const;
  virtual std::string toString() const;
private:
//  Interp::Interp *var_; // TODO: Fix
};


// TODO: add accessors for left and right
class VecVecAddExpr : public VecExpr {
public:
  VecVecAddExpr(coords::VecVecAddExpr*, domain::VecVecAddExpr*);
  const ast::VecVecAddExpr *getVecVecAddExpr();
  virtual std::string toString() const;
private:
  interp::Interp *mem_;
  interp::Interp *arg_;
};




/*
Superclass. Abstract
*/
class Vector : public VecExpr {
public:
  Vector(coords::Vector*, domain::Vector*); // tag?
  const ast::Vector *getVector() const;
  VectorCtorType getVectorType();
  virtual std::string toString() const;
  bool operator==(const Vector &other) const {
    return (clang_stmt_ == other.clang_stmt_);
  }
protected:
  const VectorCtorType tag_;
};


/*
	Vector_Var* mkVecVector_Var(coords::Vector_Var*, domain::Vector_Var*);
	Vector_Expr* mkVecVector_Expr(coords::Vector_Expr*, domain::Vector_Expr*);
	Vector_Def* mkVecVector_Def(coords::Vector_Def*, domain::Vector_Def*);
*/



// TODO: methods to get x, y, z
class Vector_Lit : public Vector {
public:
  Vector_Lit(coords::Vector_Lit*, domain::Vector_Lit*);
  virtual std::string toString() const;
private:
  float a_;
};

class Vector_Var : public Vector {
public:
  Vector_Var(coords::Vector_Var*, domain::Vector_Var*);
  virtual std::string toString() const;
  VecVarExpr *getVecVarExpr();
private:
  VecVarExpr *expr_;
};

// change name to VecVecAddExpr? Or generalize from that a bit.
class Vector_Expr : public Vector {
public:
  Vector_Expr(coords::Vector_Expr*, domain::Vector_Expr*);
  virtual std::string toString() const;
  Vector_Expr *getVector_Expr();
private:
  VecExpr *expr_;
};

/****
 * Def
 ****/

class Vector_Def : public Interp {
public:
  Vector_Def(coords::Vector_Def*, domain::Vector_Def*);
  //const clang::DeclStmt *getDeclStmt() const;
  coords::VecIdent *getIdent() const;
  coords::VecExpr *getExpr() const;
  virtual std::string toString() const;
  // Assumption here and above is that pointer
  // identity is unique and we don't need to
  // compare on these additional fields
  bool operator==(const Vector_Def &other) const {
    return (clang_decl_ == other.clang_decl_);
  }
private:
  VecIdent *bv_;
  VecExpr *be_;
};

} // namespace coords

#endif