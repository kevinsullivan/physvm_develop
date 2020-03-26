#ifndef COORDS_H
#define COORDS_H

#include "clang/AST/AST.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include <cstddef>
#include <iostream> // for cheap logging only

#include "AST.h"


/*
Code coordinate objects wrap AST 
objects to provide inherited behavior
necessary and appropriate for each
referenced code object. They give
AST objects types in our domain's
ontology. 

We maintain a bijection betwen AST and 
Coord objects: specifically between the
memory addresses of these objects. It is
thus critical not to map one AST node
address to more than one Coord object.

Code coordinates provide for ontology 
translation, between the Clang's AST 
types and our domain elements (id, 
var expr, function application expr, 
constructed vector, and definition).
*/

namespace coords {

// Ontology of Clang object types that can be 
// coordinatized. We do not currently use 
// clang::Decl but we include it here to 
// establish a path togeneralizability
//
enum ast_type { CLANG_AST_STMT, CLANG_AST_DECL }; 

class Coords {
public:
  Coords(const clang::Stmt *stmt, clang::ASTContext *context);
  Coords(const clang::Decl *decl, clang::ASTContext *context);

  bool astIsClangDecl() { return (ast_type_tag_ == CLANG_AST_DECL); }
  bool astIsClangStmt() { return (ast_type_tag_ == CLANG_AST_STMT); }

  const clang::Stmt *getClangStmt() const;
  const clang::Decl *getClangDecl() const;

  virtual bool operator==(const Coords &other) const;
  virtual std::string toString() const;
  virtual std::string getSourceLoc() const;
protected:
  ast_type ast_type_tag_;
  const clang::Stmt *clang_stmt_;
  const clang::Decl *clang_decl_;
  clang::ASTContext *context_;
};

/*************************************************************
 * Coordinate subclasses, for type checking, override behaviors
 *************************************************************/

/******
 * Ident
 ******/

class VecIdent : public Coords {
public:
  VecIdent(const ast::VecIdent *ast, clang::ASTContext *c);
  const clang::VarDecl *getVarDecl() const;
  virtual std::string toString() const;
  bool operator==(const VecIdent &other) const {
    return (clang_decl_ == other.clang_decl_);
  }
};

class FloatIdent : public Coords {
public:
  FloatIdent(const ast::VecIdent *ast, clang::ASTContext *c);
  const clang::VarDecl *getVarDecl() const;
  virtual std::string toString() const;
  bool operator==(const FloatIdent &other) const {
    return (clang_decl_ == other.clang_decl_);
  }
};



/*****
 * Expr
 *****/

// TODO: Add a dynamic type tag here
// Abstract
class VecExpr : public Coords {
public:
  VecExpr(const ast::VecExpr *e, clang::ASTContext *c);
  const ast::VecExpr *getExpr();
  virtual std::string toString() const;
  bool operator==(const VecExpr &other) const {
    return (clang_stmt_ == other.clang_stmt_);
  }
};

class FloatExpr : public Coords {
public:
  FloatExpr(const ast::FloatExpr *e, clang::ASTContext *c);
  const ast::FloatExpr *getExpr();
  virtual std::string toString() const;
  bool operator==(const FloatExpr &other) const {
    return (clang_stmt_ == other.clang_stmt_);
  }
};

class VecVarExpr : public VecExpr {
public:
  VecVarExpr(const ast::VecVarExpr *d, clang::ASTContext *c);
  const ast::VecVarExpr *getVecVarExpr() const;
  virtual std::string toString() const;
};

class FloatVarExpr : public FloatExpr {
public:
  FloatVarExpr(const ast::FloatVarExpr *d, clang::ASTContext *c);
  const ast::FloatVarExpr *getFloatVarExpr() const;
  virtual std::string toString() const;
};

// TODO: add accessors for left and right
class VecVecAddExpr : public VecExpr {
public:
  VecVecAddExpr(const ast::VecVecAddExpr *mce, clang::ASTContext *c, coords::VecExpr *mem, coords::VecExpr *arg);
  const ast::VecVecAddExpr *getVecVecAddExpr();
  virtual std::string toString() const;
  coords::Coords* getLeft() const { return mem_; }
  coords::Coords* getRight() const { return arg_; }

private:
  coords::Coords *mem_;
  coords::Coords *arg_;
};

class VecScalarMulExpr : public VecExpr {
public:
  VecScalarMulExpr(const ast::VecScalarMulExpr *mce, clang::ASTContext *c, coords::FloatExpr *flt, coords::VecExpr *vec);
  const ast::VecScalarMulExpr *getVecScalarMulExpr();
  virtual std::string toString() const;
  coords::Coords* getLeft() const { return flt_; }
  coords::Coords* getRight() const { return vec_; }

private:
  coords::Coords *flt_;
  coords::Coords *vec_;
};

class FloatFloatAddExpr : public FloatExpr {
public:
  FloatFloatAddExpr(const ast::FloatFloatAddExpr *mce, clang::ASTContext *c, coords::FloatExpr *lhs, coords::FloatExpr *rhs);
  const ast::FloatFloatAddExpr *getFloatFloatAddExpr();
  virtual std::string toString() const;
  coords::Coords* getLeft() const { return lhs_; }
  coords::Coords* getRight() const { return rhs_; }

private:
  coords::Coords *lhs_;
  coords::Coords *rhs_;
};

class FloatFloatMulExpr : public FloatExpr {
public:
  FloatFloatMulExpr(const ast::FloatFloatMulExpr *mce, clang::ASTContext *c, coords::FloatExpr *lhs, coords::FloatExpr *rhs);
  const ast::FloatFloatMulExpr *getFloatFloatMulExpr();
  virtual std::string toString() const;
  coords::Coords* getLeft() const { return lhs_; }
  coords::Coords* getRight() const { return rhs_; }

private:
  coords::Coords *lhs_;
  coords::Coords *rhs_;
};


/*************
* VecParenExpr
**************/

// Should hold coordinates of child expression
class VecParenExpr : public VecExpr {
  public:
  VecParenExpr(const ast::VecParenExpr *vec, clang::ASTContext *c, coords::VecExpr *expr);
  const coords::VecExpr *getVecExpr() const; 
  virtual std::string toString() const;
  bool operator==(const VecParenExpr &other) const {
      return (clang_stmt_ == other.clang_stmt_);
  }
  protected:
    coords::VecExpr *expr_;
};

class FloatParenExpr : public FloatExpr {
  public:
  FloatParenExpr(const ast::FloatParenExpr *flt, clang::ASTContext *c, coords::FloatExpr *expr);
  const coords::FloatExpr *getFloatExpr() const; 
  virtual std::string toString() const;
  bool operator==(const FloatParenExpr &other) const {
      return (clang_stmt_ == other.clang_stmt_);
  }
  protected:
    coords::FloatExpr *expr_;
};


/*******
* Vector
********/

enum VectorCtorType { VEC_CTOR_LIT, VEC_CTOR_EXPR, VEC_CTOR_VAR };
enum FloatCtorType { FLOAT_CTOR_LIT, FLOAT_CTOR_EXPR, FLOAT_CTOR_VAR };

// Superclass. Abstract
class Vector : public VecExpr {
public:
  Vector(const ast::Vector *vec, clang::ASTContext *c, coords::VectorCtorType tag);
  const ast::Vector *getVector() const;
  VectorCtorType getVectorType();
  virtual std::string toString() const;
  bool operator==(const Vector &other) const {
    return (clang_stmt_ == other.clang_stmt_);
  }
protected:
  const VectorCtorType tag_;
};

class Float : public FloatExpr {
public:
  Float(const ast::Float *vec, clang::ASTContext *c, coords::FloatCtorType tag);
  const ast::Float *getFloat() const;
  FloatCtorType getFloatType();
  virtual std::string toString() const;
  bool operator==(const Float &other) const {
    return (clang_stmt_ == other.clang_stmt_);
  }
protected:
  const FloatCtorType tag_;
};

// TODO: methods to get x, y, z
class Vector_Lit : public Vector {
public:
  Vector_Lit(const ast::Vector_Lit *ast, clang::ASTContext *c, ast::Scalar x, ast::Scalar y, ast::Scalar z);
  virtual std::string toString() const;
private:
  ast::Scalar x_;
  ast::Scalar y_;
  ast::Scalar z_;
};

class Float_Lit : public Float {
public:
  Float_Lit(const ast::Float_Lit *ast, clang::ASTContext *c, ast::Scalar scalar);
  virtual std::string toString() const;
private:
  ast::Scalar scalar_;
};


class Vector_Var : public Vector {
public:
  Vector_Var(const ast::Vector_Var *ast, clang::ASTContext *c, coords::VecVarExpr *expr);
  virtual std::string toString() const;
  VecVarExpr *getVecVarExpr();
private:
  VecVarExpr *expr_;
};


class Float_Var : public Float {
public:
  Float_Var(const ast::Float_Var *ast, clang::ASTContext *c, coords::FloatVarExpr *expr);
  virtual std::string toString() const;
  FloatVarExpr *getFloatVarExpr();
private:
  FloatVarExpr *expr_;
};


// TODO: change name to VecVecAddExpr?
class Vector_Expr : public Vector {
public:
  Vector_Expr(const ast::Vector_Expr *ast, clang::ASTContext *c, coords::VecExpr *expr);
  virtual std::string toString() const;
  Vector_Expr *getVector_Expr();
private:
  VecExpr *expr_;
};


class Float_Expr : public Float {
public:
  Float_Expr(const ast::Float_Expr *ast, clang::ASTContext *c, coords::FloatExpr *expr);
  virtual std::string toString() const;
  Float_Expr *getFloat_Expr();
private:
  FloatExpr *expr_;
};

/****
 * Def
 ****/

class Vector_Def : public Coords {
public:
  Vector_Def(const ast::Vector_Def *def, clang::ASTContext *c, coords::VecIdent *id,
             coords::VecExpr *expr);
  coords::VecIdent *getIdent() const;
  coords::VecExpr *getExpr() const;
  virtual std::string toString() const;
  bool operator==(const Vector_Def &other) const {
    return (clang_decl_ == other.clang_decl_);
  }
private:
  VecIdent *id_;
  VecExpr *expr_;
};

class Float_Def : public Coords {
public:
  Float_Def(const ast::Float_Def *def, clang::ASTContext *c, coords::FloatIdent *id,
             coords::FloatExpr *expr);
  coords::FloatIdent *getIdent() const;
  coords::FloatExpr *getExpr() const;
  virtual std::string toString() const;
  bool operator==(const Float_Def &other) const {
    return (clang_decl_ == other.clang_decl_);
  }
private:
  FloatIdent *id_;
  FloatExpr *expr_;
};


} // namespace coords

#endif