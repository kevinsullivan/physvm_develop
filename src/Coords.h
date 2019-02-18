#ifndef COORDS_H
#define COORDS_H

#include "AST.h"
#include "clang/AST/AST.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include <cstddef>
#include <iostream> // for cheap logging only

/*
Code coordinate objects wrap AST 
objects to provide inherited behavior
necessary and appropriate for each
referenced code object. They give
these objects types in our domain
typed ontology. An invariant of the 
design is that AST nodes are properly
characrterized by coordinate objects.

Code coordinates thus also provide for ontology translation, between the AST types used to represent pertinent 
code elements, and the AST types used to represent domain elements (id, var, expr, value, def).

Here the AST language a domain-driven 
projection of Clang. The domain 
language, as is clear, is rather one 
of vector space expressions, values, 
identifiers, and definitions.

Code coordinates are mapped to domain 
elements via a relation represented 
externally to Coords objects, namely 
the coords2domain relation(s). ASTs 
are mapped to Coords by the external ast2coordinates relations. The mapping from coordinates back to to AST objects 
is implemented by references contained 
within coords objects. Each such object
represents with dynamic state the kind of AST-level object it maps to, and it provides a pointer back to that object.

The challenge is to get precisely typed references to AST elements back from Coords objects. But in the current application, we don't really need to do so. In future, dynamic casts seem likely to be useful.
*/

namespace coords {

// Ontology of code object types that can be coordinatized
// clang::Decl unused by Peirce, here for generalizability
//
enum ast_type { CLANG_AST_STMT, CLANG_AST_DECL };

class Coords {
public:
  Coords(const clang::Stmt *stmt);
  Coords(const clang::Decl *decl);

  const clang::Stmt *getClangStmt() const;
  const clang::Decl *getClangDecl() const;

  virtual bool operator==(const Coords &other) const;
  virtual std::string toString() const;

  bool astIsClangDecl() { return (ast_type_tag_ == CLANG_AST_DECL); }

  // Remember: Clang Expr inherits from Stmt
  bool astIsClangStmt() { return (ast_type_tag_ == CLANG_AST_STMT); }

private:
  ast_type ast_type_tag_;
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


/***
**** TODO: Change types in all methods to ast:: abstractions.
***/

class VecIdent : public Coords {
public:
  VecIdent(ast::VecIdent *ast);
  clang::VarDecl *getVarDecl();
  virtual std::string toString() const;
};

/*****
 * Expr
 *****/

// TODO: Add a dynamic type tag here
// Abstract
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

class VecLitExpr : public Coords {};
*/

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
  VecVecAddExpr(const clang::CXXMemberCallExpr *mce, coords::VecExpr *mem, coords::VecExpr *arg);
  clang::CXXMemberCallExpr *getCXXMemberCallExpr();
  virtual std::string toString() const;

private:
  coords::Coords *mem_;
  coords::Coords *arg_;
};

enum VectorCtorType { VEC_CTOR_LIT, VEC_CTOR_EXPR, VEC_CTOR_VAR };

/*
Superclass. Abstract
*/
class Vector : public VecExpr {
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
  Vector_Lit(const clang::CXXConstructExpr *ast, ast::Scalar a);
  virtual std::string toString() const;

private:
  float a_;
};

class Vector_Var : public Vector {
public:
  Vector_Var(clang::CXXConstructExpr *ast, const coords::VecVarExpr *expr);
  virtual std::string toString() const;
  VecVarExpr *getVecVarExpr();

private:
  VecVarExpr *expr_;
};

// change name to VecVecAddExpr? Or generalize from that a bit.
class Vector_Expr : public Vector {
public:
  Vector_Expr(const clang::CXXConstructExpr ast, coords::Vector_Expr *expr);
  virtual std::string toString() const;
  Vector_Expr *getVector_Expr();

private:
  Vector_Expr *expr_;
};

/****
 * Def
 ****/

class Vector_Def : public Coords {
public:
  Vector_Def(const clang::DeclStmt def, coords::VecIdent *bv,
             coords::VecExpr *be);
  const clang::DeclStmt *getDeclStmt() const;
  coords::VecIdent *getIdent() const;
  coords::VecExpr *getExpr() const;
  virtual std::string toString() const;

private:
  VecIdent *bv_;
  VecExpr *be_;
};

} // namespace coords

#endif