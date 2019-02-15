#ifndef CODECOORDS_H
#define CODECOORDS_H

#include "clang/AST/AST.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include <cstddef>
#include <iostream> // for cheap logging only
#include "AST.h"


//using namespace clang;
//using namespace clang::ast_matchers;
//using namespace std;

namespace coords {

/*
ABSTRACT-ISH BASE CLASS FOR ALL COORDS OBJECTS
Instances serve as keys linking throughout system
*/

enum ast_type { EXPR, STMT, DECL };

// TODO: Change name to , as can now be either EXPR or STMT
class VecExpr {
public:
  VecExpr() : expr_(NULL) {}
  VecExpr(const clang::Expr *expr) : expr_(expr) { ast_type_ = EXPR; }
  VecExpr(const clang::Stmt *decl) : stmt_(decl) { ast_type_ = STMT; }
  VecExpr(const clang::Decl *decl) : decl_(decl) { ast_type_ = DECL; }

  // TODO: Currently only using clang::Expr class. Why?
  //
  const clang::Expr *get() const { return expr_; }

  bool operator==(const VecExpr &other) const {
    if (ast_type_ == EXPR) {
      return (expr_ == other.expr_);
    } else if (ast_type_ == STMT) {
      return (stmt_ == other.stmt_);
    } else {
      return (decl_ == other.decl_);
    }
  }
  virtual std::string toString() const {
    return "::toPrint: Error: should not be called.";
  }

private:
  ast_type ast_type_;
  const clang::Expr *expr_;
  const clang::Stmt *stmt_;
  const clang::Decl *decl_;
};

struct VecExprHasher {
  std::size_t operator()(const VecExpr &k) const {
    std::size_t hash = 10101010;
    // TODO Fix hash function
    return hash;
  }
};

// TODO: this is ctor; separate contents
class VecLitExpr : public VecExpr {
public:
  VecLitExpr(const ast::VecLitExpr *constrExpr)
      : VecExpr(constrExpr), constrExpr_(constrExpr) {}
  const ast::VecLitExpr *get() const { return constrExpr_; }

  bool operator==(const VecLitExpr &other) const {

    return (constrExpr_ == other.constrExpr_);
  }
  virtual std::string toString() const { return "(mk_vector 0)"; }

private:
  const ast::VecLitExpr *constrExpr_;
};

struct VecLitExprHasher {
  std::size_t operator()(const VecLitExpr &k) const {
    // TODO -- fix
    std::size_t hash = 10101010;
    return hash;
  }
};

//---------------

// VecIdent implemented as VarDecl
class VecIdent : public VecExpr {
public:
  VecIdent(const ast::VecIdent *ident)
      : VecExpr(ident), ident_(ident) {}

  const ast::VecIdent *getAST() const { return ident_; }

  // AST node address determines identity
  bool operator==(const VecIdent &other) const {
    return (ident_ == other.ident_);
  }
  virtual std::string toString() const { 
    return ident_->getNameAsString(); 
  }

private:
  const ast::VecIdent *ident_;
};

struct VecIdentHasher {
  std::size_t operator()(const VecIdent &k) const {
    std::size_t hash = 101010;
    // TODO Fix hash function
    return hash;
  }
};

// ToDo -- change name to VariableExpr (implemented as VecVarExpr)

class VecVarExpr : public VecExpr {
public:
  VecVarExpr(const ast::VecVarExpr *varDeclRef)
      : VecExpr(varDeclRef), varDeclRef_(varDeclRef) {}
  const ast::VecVarExpr *getVecVarExpr() const { return varDeclRef_; }

  // for now, an address-based equality predicate
  bool operator==(const VecVarExpr &other) const {
    return (varDeclRef_ == other.varDeclRef_);
  }
  virtual std::string toString() const {
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

class VecVecAddExpr : public VecExpr {
public:
  VecVecAddExpr(ast::VecVecAddExpr *exp,
                const coords::VecExpr *left, 
                const coords::VecExpr *right)
      : VecExpr(exp), cxxMemberCallExpr_(exp), left_(left), right_(right) {}
  ast::VecVecAddExpr *getCXXMemberCallExpr() const {
    return cxxMemberCallExpr_;
  }

  // for now, an address-based equality predicate
  bool operator==(const VecVecAddExpr &other) const {
    return (cxxMemberCallExpr_ == other.cxxMemberCallExpr_);
  }
  virtual std::string toString() const {
    return "add (" + left_->toString() + ") (" + right_->toString() + ")";
  }

private:
  ast::VecVecAddExpr *cxxMemberCallExpr_;
  const coords::VecExpr *left_;
  const coords::VecExpr *right_;
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


/*
// TODO weak typing of Expr argument
class AddConstruct : public VecExpr {
public:
  AddConstruct(ast::VecCtor*constrExpr,
                      const VecExpr *addExpr)
      : VecExpr(constrExpr), constrExpr_(constrExpr), addExpr_(addExpr) {}
  ast::VecCtor*get() const { return constrExpr_; }

  // for now, an address-based equality predicate
  bool operator==(const AddConstruct &other) const {

    return (constrExpr_ == other.constrExpr_);
  }
  virtual std::string toString() const { return "AddConstructNode"; }

private:
  ast::VecCtor*constrExpr_;
  const VecExpr *addExpr_;
  ;
};
*/

// TODO weak typing of Expr argument
class Vector : public VecExpr {
public:
  Vector(const ast::Vector *constrExpr)
      : VecExpr(constrExpr), constrExpr_(constrExpr) {}
  const ast::Vector *get() const { return constrExpr_; }

  // for now, an address-based equality predicate
  bool operator==(const Vector &other) const {

    return (constrExpr_ == other.constrExpr_);
  }
  virtual std::string toString() const { return "Vector"; }

private:
  const ast::Vector *constrExpr_;
  const VecExpr *expr_;
  ;
};

struct VectorHasher {
  std::size_t operator()(const Vector &k) const {
    // TODO -- fix
    std::size_t hash = 10101010;
    return hash;
  }
};

// TODO -- VecDef hides VarDecl
class VecDef : public VecExpr {
public:
  VecDef(const ast::VecDef *declStmt, const coords::VecIdent *bv, const coords::VecExpr *be)
      : declStmt_(declStmt), bv_(bv), be_(be), VecExpr(declStmt) {}

  const ast::VecDef *getAST() const { return declStmt_; }

  // AST node address-based equality predicate
  bool operator==(const VecDef &other) const {
    return (declStmt_ == other.declStmt_);
  }
  virtual std::string toString() const { return "VecDef (STUB: refine)"; }

private:
  const ast::VecDef *declStmt_;
  const VecIdent *bv_;
  const VecExpr *be_;
};

struct VecDefHasher {
  std::size_t operator()(const VecDef &k) const {
    std::size_t hash = 101010;
    // TODO Fix hash function
    return hash;
  }
};

} // namespace codecoords


#endif