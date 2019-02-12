#ifndef CODECOORDS_H
#define CODECOORDS_H

#include "clang/AST/AST.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include <cstddef>
#include <iostream> // for cheap logging only

using namespace clang;
using namespace clang::ast_matchers;
using namespace std;

namespace coords {

/*
ABSTRACT
Objects of these class will be "keys" in an interpretation.
Subclasses should be defined for each kind of AST node to
be lifted to a corresponding domain type.
*/

enum ast_type { EXPR, STMT, DECL };

// TODO: Change name to ASTNode, as can now be either EXPR or STMT
class ExprASTNode {
public:
  ExprASTNode() : expr_(NULL) {}
  ExprASTNode(const clang::Expr *expr) : expr_(expr) { ast_type_ = EXPR; }
  ExprASTNode(const clang::Stmt *decl) : stmt_(decl) { ast_type_ = STMT; }
  ExprASTNode(const clang::Decl *decl) : decl_(decl) { ast_type_ = DECL; }
  const clang::Expr *getASTNode() const { return expr_; }
  bool operator==(const ExprASTNode &other) const {
    if (ast_type_ == EXPR) {
      return (expr_ == other.expr_);
    } else if (ast_type_ == STMT) {
      return (stmt_ == other.stmt_);
    } else {
      return (decl_ == other.decl_);
    }
  }
  virtual string toString() const {
    return "ASTNode::toPrint: Error: should not be called.";
  }

private:
  ast_type ast_type_;
  const clang::Expr *expr_;
  const clang::Stmt *stmt_;
  const clang::Decl *decl_;
};

struct ExprASTNodeHasher {
  std::size_t operator()(const ExprASTNode &k) const {
    std::size_t hash = 10101010;
    // TODO Fix hash function
    return hash;
  }
};

// TODO -- don't need to store pointers in superclass
// TODO -- change name to LitExprASTNode
// TODO -- Fix naming based on current arg type
class LitASTNode : public ExprASTNode {
public:
  LitASTNode(const clang::CXXConstructExpr *constrExpr)
      : ExprASTNode(constrExpr), constrExpr_(constrExpr) {}
  const clang::CXXConstructExpr *getASTNode() const { return constrExpr_; }

  // for now, an address-based equality predicate
  bool operator==(const LitASTNode &other) const {

    return (constrExpr_ == other.constrExpr_);
  }
  virtual string toString() const { return "(mk_vector 0)"; }

private:
  const clang::CXXConstructExpr *constrExpr_;
};

struct LitASTNodeHasher {
  std::size_t operator()(const LitASTNode &k) const {
    // TODO -- fix
    std::size_t hash = 10101010;
    return hash;
  }
};

//---------------

// Identifier implemented as VarDecl
class VecIdent : public ExprASTNode {
public:
  VecIdent(const clang::VarDecl *varDecl)
      : ExprASTNode(varDecl), varDecl_(varDecl) {}
  const clang::VarDecl *getVarDecl() const { return varDecl_; }

  // for now, an address-based equality predicate
  bool operator==(const VecIdent &other) const {
    return (varDecl_ == other.varDecl_);
  }
  virtual string toString() const { return varDecl_->getNameAsString(); }

private:
  const clang::VarDecl *varDecl_;
};

struct IdentifierASTNodeHasher {
  std::size_t operator()(const VecIdent &k) const {
    std::size_t hash = 101010;
    // TODO Fix hash function
    return hash;
  }
};

// ToDo -- change name to VariableExpr (implemented as VarDeclRef)

class VarDeclRefASTNode : public ExprASTNode {
public:
  VarDeclRefASTNode(const clang::DeclRefExpr *varDeclRef)
      : ExprASTNode(varDeclRef), varDeclRef_(varDeclRef) {}
  const clang::DeclRefExpr *getVarDeclRef() const { return varDeclRef_; }

  // for now, an address-based equality predicate
  bool operator==(const VarDeclRefASTNode &other) const {
    return (varDeclRef_ == other.varDeclRef_);
  }
  virtual string toString() const {
    return varDeclRef_->getDecl()->getNameAsString();
  }

private:
  const clang::DeclRefExpr *varDeclRef_;
};

struct VarDeclRefASTNodeHasher {
  std::size_t operator()(const VarDeclRefASTNode &k) const {
    std::size_t hash = 101010;
    // TODO Fix hash function
    return hash;
  }
};

// TODO -- Change to AddMemberCallExpr, implemented as CXXMemberCallExpr

class VectorAddExprASTNode : public ExprASTNode {
public:
  VectorAddExprASTNode(const clang::CXXMemberCallExpr *exp,
                       const ExprASTNode *left, const ExprASTNode *right)
      : ExprASTNode(exp), cxxMemberCallExpr_(exp), left_(left), right_(right) {}
  const clang::CXXMemberCallExpr *getCXXMemberCallExpr() const {
    return cxxMemberCallExpr_;
  }

  // for now, an address-based equality predicate
  bool operator==(const VectorAddExprASTNode &other) const {
    return (cxxMemberCallExpr_ == other.cxxMemberCallExpr_);
  }
  virtual string toString() const {
    return "add (" + left_->toString() + ") (" + right_->toString() + ")";
  }

private:
  const clang::CXXMemberCallExpr *cxxMemberCallExpr_;
  const ExprASTNode *left_;
  const ExprASTNode *right_;
};

/*
Provide has function for ExprASTNodeHasher class, as required
for the use of objects of this class as keys in a map.
*/
struct VectorAddExprASTNodeHasher {
  std::size_t operator()(const VectorAddExprASTNode &k) const {
    std::size_t hash = 101010;
    // TODO Fix hash function
    return hash;
  }
};

// TODO weak typing of ExprASTNode argument
class AddConstructASTNode : public ExprASTNode {
public:
  AddConstructASTNode(const clang::CXXConstructExpr *constrExpr,
                      const ExprASTNode *addExpr)
      : ExprASTNode(constrExpr), constrExpr_(constrExpr), addExpr_(addExpr) {}
  const clang::CXXConstructExpr *getASTNode() const { return constrExpr_; }

  // for now, an address-based equality predicate
  bool operator==(const AddConstructASTNode &other) const {

    return (constrExpr_ == other.constrExpr_);
  }
  virtual string toString() const { return "AddConstructNode"; }

private:
  const clang::CXXConstructExpr *constrExpr_;
  const ExprASTNode *addExpr_;
  ;
};

struct AddConstructASTNodeHasher {
  std::size_t operator()(const AddConstructASTNode &k) const {
    // TODO -- fix
    std::size_t hash = 10101010;
    return hash;
  }
};

// TODO -- Binding hides VarDecl
class BindingASTNode : public ExprASTNode {
public:
  BindingASTNode(const clang::DeclStmt *declStmt, const VecIdent *bv,
                 const ExprASTNode *be)
      : declStmt_(declStmt), bv_(bv), be_(be), ExprASTNode(declStmt) {}

  const clang::DeclStmt *getDeclStmt() const { return declStmt_; }

  // for now, an address-based equality predicate
  bool operator==(const BindingASTNode &other) const {
    return (declStmt_ == other.declStmt_);
  }
  virtual string toString() const { return "Binding (STUB: refine)"; }

private:
  const clang::DeclStmt *declStmt_;
  const VecIdent *bv_;
  const ExprASTNode *be_;
};

struct BindingASTNodeHasher {
  std::size_t operator()(const BindingASTNode &k) const {
    std::size_t hash = 101010;
    // TODO Fix hash function
    return hash;
  }
};

class Coords {
  public:
    Coords() {}
    const VecIdent *makeCoordsForVecIdent(const clang::VarDecl *ident);
  private:
    unordered_map<const clang::Expr *, const coords::ExprASTNode *> exprCoords_;
    unordered_map<const clang::Stmt *, const coords::ExprASTNode *> stmtCoords_;
    unordered_map<const clang::Decl *, const coords::ExprASTNode *> declCoords_;
};

} // namespace codecoords


#endif