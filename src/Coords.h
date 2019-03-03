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
are mapped to Coords by the external 
ast2coordinates relations. The mapping 
from coordinates back to to AST objects 
is implemented by references contained 
within coords objects. Each such object
represents with dynamic state the kind 
of AST-level object it maps to, and it 
provides a pointer back to that object.

The challenge is to get precisely typed 
references to AST elements back from 
Coords objects. But in the current 
application, we don't really need to do 
so. In future, dynamic casts seem likely 
to be useful.
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

protected:
  ast_type ast_type_tag_;
  const clang::Stmt *clang_stmt_;
  const clang::Decl *clang_decl_;
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

class VecIdent : public Coords {
public:
  VecIdent(const ast::VecIdent *ast);
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
  VecExpr(const clang::Expr *e);
  const clang::Expr *getExpr();
  virtual std::string toString() const;
  bool operator==(const VecExpr &other) const {
    return (clang_stmt_ == other.clang_stmt_);
  }
};


class VecVarExpr : public VecExpr {
public:
  VecVarExpr(const clang::DeclRefExpr *d);
  const clang::DeclRefExpr *getDeclRefExpr() const;
  virtual std::string toString() const;

private:
  coords::Coords *var_; // TODO: Fix
};

// TODO: add accessors for left and right?
class VecVecAddExpr : public VecExpr {
public:
  VecVecAddExpr(const clang::CXXMemberCallExpr *mce, coords::VecExpr *mem, coords::VecExpr *arg);
  const clang::CXXMemberCallExpr *getCXXMemberCallExpr();
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
  bool operator==(const Vector &other) const {
    return (clang_stmt_ == other.clang_stmt_);
  }
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
  Vector_Var(const clang::CXXConstructExpr *ast,  coords::VecVarExpr *expr);
  virtual std::string toString() const;
  VecVarExpr *getVecVarExpr();

private:
  VecVarExpr *expr_;
};

// change name to VecVecAddExpr? Or generalize from that a bit.
class Vector_Expr : public Vector {
public:
  Vector_Expr(const clang::CXXConstructExpr *ast, coords::VecExpr *expr);
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
  Vector_Def(const clang::DeclStmt *def, coords::VecIdent *bv,
             coords::VecExpr *be);
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