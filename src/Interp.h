#ifndef INTERP_H
#define INTERP_H

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
class Vector_Assign;

class ScalarIdent;
class ScalarExpr;

class ScalarVarExpr;
class VecScalarMulExpr;

class Scalar;
class Scalar_Lit;
class Scalar_Var;
class Scalar_Expr;
class Scalar_Def;
class Scalar_Assign;


class VecParenExpr;
class ScalarParenExpr;

class TransformIdent;
class TransformExpr;

class TransformVarExpr;
class TransformParenExpr;

class TransformVecApplyExpr;
class TransformTransformComposeExpr;

class Transform;
class Transform_Lit;
class Transform_Var;
class Transform_Expr;
class Transform_Def;
class Transform_Assign;

enum domType
{
  dom_vecIdent_type,
  dom_vecExpr_type,
  dom_vector_type,
  dom_vector_def_type,
  dom_vector_assign_type,

  dom_floatIdent_type,
  dom_floatExpr_type,
  dom_float_type,
  dom_float_def_type,
  dom_float_assign_type,

  dom_transformIdent_type,
  dom_transformExpr_type,
  dom_transform_type,
  dom_transform_def_type,
  dom_transform_assign_type
};

class Interp
{
public:
  Interp(coords::VecIdent *c, domain::VecIdent *d);
  Interp(coords::VecExpr *c, domain::VecExpr *d);
  Interp(coords::Vector *c, domain::Vector *d);
  Interp(coords::Vector_Def *c, domain::Vector_Def *d);
  Interp(coords::Vector_Assign *c, domain::Vector_Assign *d);

  Interp(coords::ScalarIdent *c, domain::ScalarIdent *d);
  Interp(coords::ScalarExpr *c, domain::ScalarExpr *d);
  Interp(coords::Scalar *c, domain::Scalar *d);
  Interp(coords::Scalar_Def *c, domain::Scalar_Def *d);
  Interp(coords::Scalar_Assign *c, domain::Scalar_Assign *d);

  Interp(coords::TransformIdent *c, domain::TransformIdent *d);
  Interp(coords::TransformExpr *c, domain::TransformExpr *d);
  Interp(coords::Transform *c, domain::Transform *d);
  Interp(coords::Transform_Def *c, domain::Transform_Def *d);
  Interp(coords::Transform_Assign *c, domain::Transform_Assign *d);

  virtual std::string toString() const;

//protected:
  coords::Coords *coords_;
  domType type_;
  // TODO: make it a union
  domain::VecIdent *ident_;
  domain::VecExpr *expr_;
  domain::Vector *vector_;
  domain::Vector_Def *def_;
  domain::Vector_Assign *assign_;

  domain::ScalarIdent *float_ident_;
  domain::ScalarExpr *float_expr_;
  domain::Scalar *float_;
  domain::Scalar_Def *float_def_;
  domain::Scalar_Assign *float_assign_;

  domain::TransformIdent *transform_ident_;
  domain::TransformExpr *transform_expr_;
  domain::Transform *transform_;
  domain::Transform_Def *transform_def_;
  domain::Transform_Assign *transform_assign_;
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
  virtual std::string toString() const;
  bool operator==(const VecIdent &other) const
  {
    return (ident_ == other.ident_);
  }
};

class ScalarIdent : public Interp
{
  public:
  ScalarIdent(coords::ScalarIdent *c, domain::ScalarIdent *d);
  virtual std::string toString() const;
  bool operator==(const ScalarIdent &other) const
  {
    return (ident_ == other.ident_);
  }
};

class TransformIdent : public Interp
{
  public:
  TransformIdent(coords::TransformIdent *c, domain::TransformIdent *d);
  virtual std::string toString() const;
  bool operator==(const TransformIdent &other) const
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
  bool operator==(const VecExpr &other) const
  {
    return (expr_ == other.expr_);
  }
  virtual std::string toString() const;
};

class ScalarExpr : public Interp
{
public:
  ScalarExpr(coords::ScalarExpr *, domain::ScalarExpr *);
  bool operator==(const ScalarExpr &other) const
  {
    return (expr_ == other.expr_);
  }
  virtual std::string toString() const;
};

class TransformExpr : public Interp
{
public:
  TransformExpr(coords::TransformExpr *, domain::TransformExpr *);
  bool operator==(const TransformExpr &other) const
  {
    return (expr_ == other.expr_);
  }
  virtual std::string toString() const;
};



class VecVarExpr : public VecExpr
{
public:
  VecVarExpr(coords::VecVarExpr *, domain::VecVarExpr *);
  const coords::VecVarExpr *getVecVarCoords() const;
  virtual std::string toString() const;
};

class ScalarVarExpr : public ScalarExpr
{
public:
  ScalarVarExpr(coords::ScalarVarExpr *, domain::ScalarVarExpr *);
  const coords::ScalarVarExpr *getScalarVarCoords() const;
  virtual std::string toString() const;
};

class TransformVarExpr : public TransformExpr
{
public:
  TransformVarExpr(coords::TransformVarExpr *, domain::TransformVarExpr *);
  const coords::TransformVarExpr *getTransformVarCoords() const;
  virtual std::string toString() const;
};


// TODO: add accessors for left and right
class VecVecAddExpr : public VecExpr
{
public:
  VecVecAddExpr(coords::VecVecAddExpr *, domain::VecVecAddExpr *,
                interp::Interp *mem, interp::Interp *arg);
  virtual std::string toString() const;

private:
  interp::Interp *mem_;
  interp::Interp *arg_;
};

class ScalarScalarAddExpr : public ScalarExpr
{
public:
  ScalarScalarAddExpr(coords::ScalarScalarAddExpr *, domain::ScalarScalarAddExpr *,
                interp::Interp *lhs, interp::Interp *rhs);
  virtual std::string toString() const;

private:
  interp::Interp *lhs_;
  interp::Interp *rhs_;
};

class ScalarScalarMulExpr : public ScalarExpr
{
public:
  ScalarScalarMulExpr(coords::ScalarScalarMulExpr *, domain::ScalarScalarMulExpr *,
                interp::Interp *lhs, interp::Interp *rhs);
  virtual std::string toString() const;

private:
  interp::Interp *lhs_;
  interp::Interp *rhs_;
};


class VecScalarMulExpr : public VecExpr
{
public:
  VecScalarMulExpr(coords::VecScalarMulExpr *, domain::VecScalarMulExpr *,
                interp::Interp *vec, interp::Interp *flt);
  virtual std::string toString() const;

private:
  interp::Interp *vec_;
  interp::Interp *flt_;
};


class TransformVecApplyExpr : public VecExpr
{
public:
  TransformVecApplyExpr(coords::TransformVecApplyExpr *, domain::TransformVecApplyExpr *,
                interp::Interp *tfm, interp::Interp *vec);
  virtual std::string toString() const;

private:
  interp::Interp *tfm_;
  interp::Interp *vec_;
};


class TransformTransformComposeExpr : public TransformExpr
{
public:
  TransformTransformComposeExpr(coords::TransformTransformComposeExpr *, domain::TransformTransformComposeExpr *,
                interp::Interp *outer, interp::Interp *inner);
  virtual std::string toString() const;

private:
  interp::Interp *outer_;
  interp::Interp *inner_;
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

class ScalarParenExpr : public ScalarExpr
{
public:
  ScalarParenExpr(coords::ScalarParenExpr *, domain::ScalarParenExpr *, interp::ScalarExpr *expr_);
  virtual std::string toString() const;
  interp::ScalarExpr *getScalar_Expr() const { return paren_expr_; }

private:
  interp::ScalarExpr *paren_expr_;
};

class TransformParenExpr : public TransformExpr
{
public:
  TransformParenExpr(coords::TransformParenExpr *, domain::TransformParenExpr *, interp::TransformExpr *expr_);
  virtual std::string toString() const;
  interp::TransformExpr *getTransform_Expr() const { return paren_expr_; }

private:
  interp::TransformExpr *paren_expr_;
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

class Scalar : public Interp
{
public:
  Scalar(coords::Scalar *, domain::Scalar *); // tag?
  const ast::Scalar *getScalar() const;
  coords::ScalarCtorType getScalarType();
  virtual std::string toString() const;
};

class Transform : public Interp
{
public:
  Transform(coords::Transform *, domain::Transform *); // tag?
  const ast::Transform *getTransform() const;
  coords::TransformCtorType getTransformType();
  virtual std::string toString() const;
};


// TODO: methods to get x, y, z
class Vector_Lit : public Vector
{
public:
  Vector_Lit(coords::Vector_Lit *, domain::Vector_Lit *);
  virtual std::string toString() const;
};

class Scalar_Lit : public Scalar
{
public:
  Scalar_Lit(coords::Scalar_Lit *, domain::Scalar_Lit *);
  virtual std::string toString() const;
};

class Transform_Lit : public Transform
{
public:
  Transform_Lit(coords::Transform_Lit *, domain::Transform_Lit *, interp::Interp *, interp::Interp *, interp::Interp *);
  virtual std::string toString() const;
private:
  interp::Interp* arg1_;
  interp::Interp* arg2_;
  interp::Interp* arg3_;
};


class Vector_Var : public Vector
{
public:
  Vector_Var(coords::Vector_Var *, domain::Vector_Var *);
  virtual std::string toString() const;
  //VecVarExpr *getVecVarExpr() const;
};

class Scalar_Var : public Scalar
{
public:
  Scalar_Var(coords::Scalar_Var *, domain::Scalar_Var *);
  virtual std::string toString() const;

};

class Transform_Var : public Transform
{
public:
  Transform_Var(coords::Transform_Var *, domain::Transform_Var *);
  virtual std::string toString() const;

};

// change name to VecVecAddExpr? Or generalize from that a bit.
class Vector_Expr : public Vector
{
public:
  Vector_Expr(coords::Vector_Expr *, domain::Vector_Expr *, interp::Interp *expr_interp);
  virtual std::string toString() const;
  interp::Interp *getVector_Expr() const { return expr_interp_; }

private:
  interp::Interp *expr_interp_;
};

class Scalar_Expr : public Scalar
{
public:
  Scalar_Expr(coords::Scalar_Expr *, domain::Scalar_Expr *, interp::ScalarExpr *expr_interp);
  virtual std::string toString() const;
  interp::ScalarExpr *getScalar_Expr() const { return expr_interp_; }

private:
  interp::ScalarExpr *expr_interp_;
};

class Transform_Expr : public Transform
{
public:
  Transform_Expr(coords::Transform_Expr *, domain::Transform_Expr *, interp::TransformExpr *expr_interp);
  virtual std::string toString() const;
  interp::TransformExpr *getTransform_Expr() const { return expr_interp_; }

private:
  interp::TransformExpr *expr_interp_;
};

/****
 * Def
 ****/

class Vector_Def : public Interp
{
public:
  Vector_Def(coords::Vector_Def *, domain::Vector_Def *, interp::VecIdent *id, interp::Interp *vec);
  virtual std::string toString() const;

private:
  interp::VecIdent *id_;
  interp::Interp *vec_;
};

class Scalar_Def : public Interp
{
public:
  Scalar_Def(coords::Scalar_Def *, domain::Scalar_Def *, interp::ScalarIdent *id, interp::Interp *flt);
  virtual std::string toString() const;

private:
  interp::ScalarIdent *id_;
  interp::Interp *flt_;
};

class Transform_Def : public Interp
{
public:
  Transform_Def(coords::Transform_Def *, domain::Transform_Def *, interp::TransformIdent *id, interp::Interp *tfm);
  virtual std::string toString() const;

private:
  interp::TransformIdent *id_;
  interp::Interp *tfm_;
};

class Vector_Assign : public Interp
{
public:
  Vector_Assign(coords::Vector_Assign *, domain::Vector_Assign *, interp::VecVarExpr *id,  interp::Interp *ve);
  virtual std::string toString() const;

private:
  interp::VecVarExpr *id_;
  interp::Interp *vec_;
};

class Scalar_Assign : public Interp
{
public:
  Scalar_Assign(coords::Scalar_Assign *, domain::Scalar_Assign *, interp::ScalarVarExpr *id,  interp::Interp *flt);
  virtual std::string toString() const;

private:
  interp::ScalarVarExpr *id_;
  interp::Interp *flt_;
};

class Transform_Assign : public Interp
{
public:
  Transform_Assign(coords::Transform_Assign *, domain::Transform_Assign *, interp::TransformVarExpr *id,  interp::Interp *tfm);
  virtual std::string toString() const;

private:
  interp::TransformVarExpr *id_;
  interp::Interp *tfm_;
};

} // namespace interp

#endif