#include "Coords.h"

#ifndef COORDS_H
#define COORDS_H

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

Coords::Coords(const clang::Stmt *stmt)  : 
    clang_ast_stmt_(stmt), clang_ast_decl_(NULL), ast_type_(CLANG_AST_STMT) {    
}  

Coords::Coords(const clang::Decl *decl)  : 
    clang_ast_stmt_(NULL), clang_ast_decl_(decl), ast_type_(CLANG_AST_DECL) {
}

const clang::Stmt *Coords::getClangStmt() const { 
    if (ast_type_ != CLANG_AST_STMT) {
        cerr << "clang::Stmt *Coords::getClangStmt: Error. Wrong type tag.\n";
        return NULL;
    }
    return clang_ast_stmt_; 
}

const clang::Decl *Coords::getClangDecl() const { 
    if (ast_type_ != CLANG_AST_DECL) {
        cerr << "clang::Stmt *Coords::getClangDecl: Error. Wrong type tag.\n";
        return NULL;
    }
    return clang_ast_decl_(); 
}

bool Coords::operator==(const Coords &other) const {
    if (ast_type_ == CLANG_AST_STMT) {
        return (clang_ast_stmt_ == other.clang_ast_stmt_);
    } else if (ast_type_ == CLANG_AST_DECL) {
        return (clang_ast_decl_ == other.clang_ast_decl_);
    } 
}

virtual std::string Coords::toString() const {
    return "Coords::toPrint: Error: should not be called.";
}

struct CoordsHasher {
  std::size_t operator()(const Coords &k) const {
    std::size_t hash = 10101010;
    // TODO Fix hash function
    return hash;
  }
};

/******************************************************
* For type checking Coords for different kinds of nodes.
* Uses domain language ontology.
******************************************************/ 

class VecLitExpr : public Coords {
public:
  VecLitExpr(const ast::VecLitExpr *v) : Coords(v) {}
  virtual std::string toString() const { return "(mk_vector 0)"; }
};

// VecIdent implemented as VarDecl
class VecIdent : public Coords {
public:
  VecIdent(const ast::VecIdent *ident)
      : Coords(ident), ident_(ident) {}

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

class VecVarExpr : public Coords {
public:
  VecVarExpr(const ast::VecVarExpr *varDeclRef)
      : Coords(varDeclRef), varDeclRef_(varDeclRef) {}
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

class VecVecAddExpr : public Coords {
public:
  VecVecAddExpr(ast::VecVecAddExpr *exp,
                const coords::VecExpr *left, 
                const coords::VecExpr *right)
      : Coords(exp), cxxMemberCallExpr_(exp), left_(left), right_(right) {}
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
class AddConstruct : public Coords {
public:
  AddConstruct(ast::VecCtor*constrExpr,
                      const Coords *addExpr)
      : Coords(constrExpr), constrExpr_(constrExpr), addExpr_(addExpr) {}
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


enum VectorCtorType { VEC_CTOR_LIT, VEC_CTOR_EXPR, VEC_CTOR_VAR };


// TODO weak typing of Expr argument
class Vector {
public:
  Vector(const ast::Vector *ast), tag_(tag)
      : Coords(ast), tag_(tag) {}
  const ast::Vector *get() const { return constrExpr_; }

  // for now, an address-based equality predicate
  bool operator==(const Vector &other) const {

    return (constrExpr_ == other.constrExpr_);
  }
  virtual std::string toString() const { return "Vector"; }

protected:
    const VectorCtorType tag_;
    const ast::Vector *ast_;
    const ast::VecExpr *expr_;    // Vector_Expr
    const ast::VecVarExpr *var_;  // Vector_Var
};

struct VectorHasher {
  std::size_t operator()(const Vector &k) const {
    // TODO -- fix
    std::size_t hash = 10101010;
    return hash;
  }
};

// TODO weak typing of Expr argument
class Vector_Lit : public Coords {
public:
  Vector_Lit(const ast::Vector *ast) : Coords(ast), tag_(VEC_CTOR_LIT) {}
  const ast::Vector *get() const { return ast_; }

  // for now, an address-based equality predicate
  bool operator==(const Vector &other) const {

    return (ast_ == other.ast_);
  }
  virtual std::string toString() const { return "Vector_Lit::toString() STUB."; }

private:
};

struct Vector_LitHasher {
  std::size_t operator()(const Vector &k) const {
    // TODO -- fix
    std::size_t hash = 10101010;
    return hash;
  }
};

// TODO weak typing of Expr argument
class Vector_Expr : public Coords {
public:
  Vector_Expr(const ast::Vector *constrExpr)
      : Coords(constrExpr), constrExpr_(constrExpr) {}
  const ast::Vector *get() const { return constrExpr_; }

  // for now, an address-based equality predicate
  bool operator==(const Vector &other) const {

    return (constrExpr_ == other.constrExpr_);
  }
  virtual std::string toString() const { return "Vector"; }

private:
  const VecExpr *expr_;
};

struct Vector_ExprHasher {
  std::size_t operator()(const Vector &k) const {
    // TODO -- fix
    std::size_t hash = 10101010;
    return hash;
  }
};

// TODO -- VecDef hides VarDecl
class VecDef : public Coords {
public:
  VecDef(const ast::VecDef *declStmt, const coords::VecIdent *bv, const coords::Coords *be)
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
