#ifndef INTERP_H
#define INTERP_H

#include "clang/AST/AST.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include <cstddef>
#include <iostream> // for cheap logging only

#include "Coords.h"
#include "AST.h"
#include "Domain.h"

namespace interp
{

class VecIdent;
class VecExpr;
class VecVarExpr;
class VecVecAddExpr;
class Vector;
class Vector_Lit;
class Vector_Var;
class Vector_Expr;
class Vector_Def;

enum domType
{
  dom_vecIdent_type,
  dom_vecExpr_type,
  dom_vector_type,
  dom_vector_def_type
};

class Interp
{
public:
  Interp(coords::VecIdent *c, domain::VecIdent *d);
  Interp(coords::VecExpr *c, domain::VecExpr *d);
  Interp(coords::Vector *c, domain::Vector *d);
  Interp(coords::Vector_Def *c, domain::Vector_Def *d);
  virtual std::string toString() const;

protected:
  coords::Coords *coords_;
  domType type_;
  // TODO: make it a union
  domain::VecIdent *ident_;
  domain::VecExpr *expr_;
  domain::Vector *vector_;
  domain::Vector_Def *def_;
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

class VecIdent : public Interp
{
  public:
  VecIdent(coords::VecIdent *c, domain::VecIdent *d);
  const clang::VarDecl *getVarDecl() const;
  virtual std::string toString() const;
  bool operator==(const VecIdent &other) const
  {
    return (ident_ == other.ident_);
  }
};

/*****
 * Expr
 *****/

// TODO: Add a dynamic type tag here
// Abstract
class VecExpr : public Interp
{
public:
  VecExpr(coords::VecExpr *, domain::VecExpr *);
  const ast::VecExpr *getExpr();
  bool operator==(const VecExpr &other) const
  {
    return (expr_ == other.expr_);
  }
  virtual std::string toString() const;
};

class VecVarExpr : public VecExpr
{
public:
  VecVarExpr(coords::VecVarExpr *, domain::VecVarExpr *);
  const ast::VecVarExpr *getVecVarExpr() const;
  const coords::VecVarExpr *getVecVarCoords() const;
  virtual std::string toString() const;
};

// TODO: add accessors for left and right
class VecVecAddExpr : public VecExpr
{
public:
  VecVecAddExpr(coords::VecVecAddExpr *, domain::VecVecAddExpr *,
                interp::Interp *mem, interp::Interp *arg);
  const ast::VecVecAddExpr *getVecVecAddExpr();
  virtual std::string toString() const;

private:
  interp::Interp *mem_;
  interp::Interp *arg_;
};

class VecParenExpr : public VecExpr
{
public:
  VecParenExpr(coords::VecParenExpr *, domain::VecParenExpr *, interp::VecExpr *expr_);
  virtual std::string toString() const;
  interp::VecExpr *getVector_Expr() const { return paren_expr_; }

private:
  interp::VecExpr *paren_expr_;
};

/*
Superclass. Abstract
*/
class Vector : public Interp
{
public:
  Vector(coords::Vector *, domain::Vector *); // tag?
  const ast::Vector *getVector() const;
  coords::VectorCtorType getVectorType();
  virtual std::string toString() const;
};

// TODO: methods to get x, y, z
class Vector_Lit : public Vector
{
public:
  Vector_Lit(coords::Vector_Lit *, domain::Vector_Lit *);
  virtual std::string toString() const;
};

class Vector_Var : public Vector
{
public:
  Vector_Var(coords::Vector_Var *, domain::Vector_Var *);
  virtual std::string toString() const;
  //VecVarExpr *getVecVarExpr() const;
};

// change name to VecVecAddExpr? Or generalize from that a bit.
class Vector_Expr : public Vector
{
public:
  Vector_Expr(coords::Vector_Expr *, domain::Vector_Expr *, interp::VecExpr *expr_interp);
  virtual std::string toString() const;
  interp::VecExpr *getVector_Expr() const { return expr_interp_; }

private:
  interp::VecExpr *expr_interp_;
};

/****
 * Def
 ****/

class Vector_Def : public Interp
{
public:
  Vector_Def(coords::Vector_Def *, domain::Vector_Def *, interp::VecIdent *id, interp::Vector *vec);
  virtual std::string toString() const;

private:
  interp::VecIdent *id_;
  interp::Vector *vec_;
};

} // namespace interp

#endif