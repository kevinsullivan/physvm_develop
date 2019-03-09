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


class VecVarExpr : public VecExpr {
public:
  VecVarExpr(const ast::VecVarExpr *d, clang::ASTContext *c);
  const ast::VecVarExpr *getVecVarExpr() const;
  virtual std::string toString() const;
};

// TODO: add accessors for left and right
class VecVecAddExpr : public VecExpr {
public:
  VecVecAddExpr(const ast::VecVecAddExpr *mce, clang::ASTContext *c, coords::VecExpr *mem, coords::VecExpr *arg);
  const ast::VecVecAddExpr *getVecVecAddExpr();
  virtual std::string toString() const;
private:
  coords::Coords *mem_;
  coords::Coords *arg_;
};

enum VectorCtorType { VEC_CTOR_LIT, VEC_CTOR_EXPR, VEC_CTOR_VAR };

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

class Vector_Var : public Vector {
public:
  Vector_Var(const ast::Vector_Var *ast, clang::ASTContext *c, coords::VecVarExpr *expr);
  virtual std::string toString() const;
  VecVarExpr *getVecVarExpr();
private:
  VecVarExpr *expr_;
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

} // namespace coords

#endif