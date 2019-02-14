#ifndef CODECOORDS_H
#define CODECOORDS_H

#include "clang/AST/AST.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include <cstddef>
#include <iostream> // for cheap logging only
#include "AST.h"


using namespace clang;
using namespace clang::ast_matchers;
using namespace std;

namespace coords {

/*
ABSTRACT-ISH BASE CLASS FOR ALL COORDS OBJECTS
Instances serve as keys linking throughout system
*/

enum ast_type { EXPR, STMT, DECL };

// TODO: Change name to , as can now be either EXPR or STMT
class VectorExpr {
public:
  VectorExpr() : expr_(NULL) {}
  VectorExpr(const clang::Expr *expr) : expr_(expr) { ast_type_ = EXPR; }
  VectorExpr(const clang::Stmt *decl) : stmt_(decl) { ast_type_ = STMT; }
  VectorExpr(const clang::Decl *decl) : decl_(decl) { ast_type_ = DECL; }

  const clang::Expr *get() const { return expr_; }

  bool operator==(const VectorExpr &other) const {
    if (ast_type_ == EXPR) {
      return (expr_ == other.expr_);
    } else if (ast_type_ == STMT) {
      return (stmt_ == other.stmt_);
    } else {
      return (decl_ == other.decl_);
    }
  }
  virtual string toString() const {
    return "::toPrint: Error: should not be called.";
  }

private:
  ast_type ast_type_;
  const clang::Expr *expr_;
  const clang::Stmt *stmt_;
  const clang::Decl *decl_;
};

struct VectorExprHasher {
  std::size_t operator()(const VectorExpr &k) const {
    std::size_t hash = 10101010;
    // TODO Fix hash function
    return hash;
  }
};

// TODO: this is ctor; separate contents
class VectorLit : public VectorExpr {
public:
  VectorLit(const ast::VecLitExpr *constrExpr)
      : VectorExpr(constrExpr), constrExpr_(constrExpr) {}
  const ast::VecLitExpr *get() const { return constrExpr_; }

  bool operator==(const VectorLit &other) const {

    return (constrExpr_ == other.constrExpr_);
  }
  virtual string toString() const { return "(mk_vector 0)"; }

private:
  const ast::VecLitExpr *constrExpr_;
};

struct VectorLitHasher {
  std::size_t operator()(const VectorLit &k) const {
    // TODO -- fix
    std::size_t hash = 10101010;
    return hash;
  }
};

//---------------

// Identifier implemented as VarDecl
class VecIdent : public VectorExpr {
public:
  VecIdent(const VecIdent *varDecl)
      : VectorExpr(varDecl), varDecl_(varDecl) {}
  const VecIdent *getVarDecl() const { return varDecl_; }

  // for now, an address-based equality predicate
  bool operator==(const VecIdent &other) const {
    return (varDecl_ == other.varDecl_);
  }
  virtual string toString() const { return varDecl_->getNameAsString(); }

private:
  const VecIdent *varDecl_;
};

struct IdentifierHasher {
  std::size_t operator()(const VecIdent &k) const {
    std::size_t hash = 101010;
    // TODO Fix hash function
    return hash;
  }
};

// ToDo -- change name to VariableExpr (implemented as VecVarExpr)

class VecVarExpr : public VectorExpr {
public:
  VecVarExpr(const ast::VecVarExpr *varDeclRef)
      : VectorExpr(varDeclRef), varDeclRef_(varDeclRef) {}
  const ast::VecVarExpr *getVecVarExpr() const { return varDeclRef_; }

  // for now, an address-based equality predicate
  bool operator==(const VecVarExpr &other) const {
    return (varDeclRef_ == other.varDeclRef_);
  }
  virtual string toString() const {
    return varDeclRef_->getDecl()->getNameAsString();
  }

private:
  const ast::VecVarExpr *varDeclRef_;
};

struct VecVarExprHasher {
  std::size_t operator()(const VecVarExpr &k) const {
    std::size_t hash = 101010;
    // TODO Fix hash function
    return hash;
  }
};

// TODO -- Change to AddMemberCallExpr, implemented as CXXMemberCallExpr

class VecVecAddExpr : public VectorExpr {
public:
  VecVecAddExpr(ast::VecVecAddExpr *exp,
                       const VectorExpr *left, const VectorExpr *right)
      : VectorExpr(exp), cxxMemberCallExpr_(exp), left_(left), right_(right) {}
  ast::VecVecAddExpr *getCXXMemberCallExpr() const {
    return cxxMemberCallExpr_;
  }

  // for now, an address-based equality predicate
  bool operator==(const VecVecAddExpr &other) const {
    return (cxxMemberCallExpr_ == other.cxxMemberCallExpr_);
  }
  virtual string toString() const {
    return "add (" + left_->toString() + ") (" + right_->toString() + ")";
  }

private:
  ast::VecVecAddExpr *cxxMemberCallExpr_;
  const VectorExpr *left_;
  const VectorExpr *right_;
};

/*
Provide has function for ExprHasher class, as required
for the use of objects of this class as keys in a map.
*/
struct VecVecAddExprHasher {
  std::size_t operator()(const VecVecAddExpr &k) const {
    std::size_t hash = 101010;
    // TODO Fix hash function
    return hash;
  }
};

// TODO weak typing of Expr argument
class AddConstruct : public VectorExpr {
public:
  AddConstruct(const clang::CXXConstructExpr *constrExpr,
                      const VectorExpr *addExpr)
      : VectorExpr(constrExpr), constrExpr_(constrExpr), addExpr_(addExpr) {}
  const clang::CXXConstructExpr *get() const { return constrExpr_; }

  // for now, an address-based equality predicate
  bool operator==(const AddConstruct &other) const {

    return (constrExpr_ == other.constrExpr_);
  }
  virtual string toString() const { return "AddConstructNode"; }

private:
  const clang::CXXConstructExpr *constrExpr_;
  const VectorExpr *addExpr_;
  ;
};

// TODO weak typing of Expr argument
class Vector : public VectorExpr {
public:
  Vector(const clang::CXXConstructExpr *constrExpr)
      : VectorExpr(constrExpr), constrExpr_(constrExpr) {}
  const clang::CXXConstructExpr *get() const { return constrExpr_; }

  // for now, an address-based equality predicate
  bool operator==(const Vector &other) const {

    return (constrExpr_ == other.constrExpr_);
  }
  virtual string toString() const { return "Vector"; }

private:
  const clang::CXXConstructExpr *constrExpr_;
  const VectorExpr *expr_;
  ;
};

/*
Coords.h: In constructor 'coords::Vector::Vector(const clang::CXXConstructExpr*, const coords::VectorExpr*)':
Coords.h:203:59: error: class 'coords::Vector' does not have any field named 'addExpr_'
       : Expr(constrExpr), constrExpr_(constrExpr), addExpr_(addExpr) {}
            
*/

struct VectorHasher {
  std::size_t operator()(const Vector &k) const {
    // TODO -- fix
    std::size_t hash = 10101010;
    return hash;
  }
};

// TODO -- Binding hides VarDecl
class Binding : public VectorExpr {
public:
  Binding(const VecDef *declStmt, const VecIdent *bv,
                 const VectorExpr *be)
      : declStmt_(declStmt), bv_(bv), be_(be), VectorExpr(declStmt) {}

  const VecDef *getDeclStmt() const { return declStmt_; }

  // for now, an address-based equality predicate
  bool operator==(const Binding &other) const {
    return (declStmt_ == other.declStmt_);
  }
  virtual string toString() const { return "Binding (STUB: refine)"; }

private:
  const VecDef *declStmt_;
  const VecIdent *bv_;
  const VectorExpr *be_;
};

struct BindingHasher {
  std::size_t operator()(const Binding &k) const {
    std::size_t hash = 101010;
    // TODO Fix hash function
    return hash;
  }
};

} // namespace codecoords


#endif