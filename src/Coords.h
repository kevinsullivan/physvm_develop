#ifndef COORDS_H
#define COORDS_H

#include "clang/AST/AST.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include <cstddef>
#include <iostream> // for cheap logging only
#include <string>

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
//enum ast_type { CLANG_AST_STMT, CLANG_AST_DECL }; 

struct ASTState {
public:
  ASTState(
    std::string file_id,
    std::string file_name,
    std::string file_path,
    std::string name,
    int begin_line_no,
    int begin_col_no,
    int end_line_no,
    int end_col_no
  );

  std::string file_id_;
  std::string file_name_;
  std::string file_path_;

  std::string name_; //only used for Decl. possibly subclass this, or else this property is unused elsewhere

  int begin_line_no_;
  int begin_col_no_;
  int end_line_no_;
  int end_col_no_;

  bool operator==(const ASTState& other) const {
    return 
      file_id_ == other.file_id_ and
      file_name_ == other.file_name_ and
      file_path_ == other.file_path_ and
      begin_line_no_ == other.begin_line_no_ and
      begin_col_no_ == other.begin_col_no_ and
      end_line_no_ == other.end_line_no_ and
      end_col_no_ == other.end_col_no_;
  }
};

class Coords {
public:
  Coords();

//  bool astIsClangDecl() { return (ast_type_tag_ == CLANG_AST_DECL); }
//  bool astIsClangStmt() { return (ast_type_tag_ == CLANG_AST_STMT); }

//  const clang::Stmt *getClangStmt() const;
//  const clang::Decl *getClangDecl() const;

  virtual bool operator==(const Coords &other) const;
  virtual std::string toString() const;
  virtual std::string getSourceLoc() const;

  ASTState* state_; //maybe  change this to a constructor argument
protected:
//  ast_type ast_type_tag_;
//  const clang::Stmt *clang_stmt_;
//  const clang::Decl *clang_decl_;
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
  VecIdent();
  virtual std::string toString() const;
  bool operator==(const VecIdent &other) const {
    return this->state_ == other.state_;
  }
};

class ScalarIdent : public Coords {
public:
  ScalarIdent();
  virtual std::string toString() const;
  bool operator==(const ScalarIdent &other) const {
    return this->state_ == other.state_;
  }
};

class TransformIdent : public Coords {
public:
  TransformIdent();
  virtual std::string toString() const;
  bool operator==(const TransformIdent &other) const {
    return this->state_ == other.state_;
  }
};



/*****
 * Expr
 *****/

// TODO: Add a dynamic type tag here
// Abstract
class VecExpr : public Coords {
public:
  VecExpr();
  virtual std::string toString() const;
  bool operator==(const VecExpr &other) const {
    return this->state_ == other.state_;
  }
};

class ScalarExpr : public Coords {
public:
  ScalarExpr();
  virtual std::string toString() const;
  bool operator==(const ScalarExpr &other) const {
    return this->state_ == other.state_;
  }
};

class TransformExpr : public Coords {
public:
  TransformExpr();
  virtual std::string toString() const;
  bool operator==(const TransformExpr &other) const {
    return this->state_ == other.state_;
  }
};

/*
* VAR EXPR
*/

class VecVarExpr : public VecExpr {
public:
  VecVarExpr();
  virtual std::string toString() const;
};

class ScalarVarExpr : public ScalarExpr {
public:
  ScalarVarExpr();
  virtual std::string toString() const;
};

class TransformVarExpr : public TransformExpr {
public:
  TransformVarExpr();
  virtual std::string toString() const;
};

/*
* OPERATIONS
*/

// TODO: add accessors for left and right
class VecVecAddExpr : public VecExpr {
public:
  VecVecAddExpr(coords::VecExpr *mem, coords::VecExpr *arg);
  virtual std::string toString() const;
  coords::Coords* getLeft() const { return mem_; }
  coords::Coords* getRight() const { return arg_; }

private:
  coords::Coords *mem_;
  coords::Coords *arg_;
};

class VecScalarMulExpr : public VecExpr {
public:
  VecScalarMulExpr(coords::ScalarExpr *flt, coords::VecExpr *vec);
  virtual std::string toString() const;
  coords::Coords* getLeft() const { return flt_; }
  coords::Coords* getRight() const { return vec_; }

private:
  coords::Coords *flt_;
  coords::Coords *vec_;
};

class ScalarScalarAddExpr : public ScalarExpr {
public:
  ScalarScalarAddExpr(coords::ScalarExpr *lhs, coords::ScalarExpr *rhs);
  virtual std::string toString() const;
  coords::Coords* getLeft() const { return lhs_; }
  coords::Coords* getRight() const { return rhs_; }

private:
  coords::Coords *lhs_;
  coords::Coords *rhs_;
};

class ScalarScalarMulExpr : public ScalarExpr {
public:
  ScalarScalarMulExpr(coords::ScalarExpr *lhs, coords::ScalarExpr *rhs);
  virtual std::string toString() const;
  coords::Coords* getLeft() const { return lhs_; }
  coords::Coords* getRight() const { return rhs_; }

private:
  coords::Coords *lhs_;
  coords::Coords *rhs_;
};

class TransformVecApplyExpr : public VecExpr {
public:
  TransformVecApplyExpr(coords::TransformExpr *lhs, coords::VecExpr *rhs);
  virtual std::string toString() const;
  coords::Coords* getLeft() const { return lhs_; }
  coords::Coords* getRight() const { return rhs_; }

private:
  coords::Coords *lhs_;
  coords::Coords *rhs_;
};

class TransformTransformComposeExpr : public TransformExpr {
public:
  TransformTransformComposeExpr(coords::TransformExpr *lhs, coords::TransformExpr *rhs);
  virtual std::string toString() const;
  coords::Coords* getLeft() const { return lhs_; }
  coords::Coords* getRight() const { return rhs_; }

private:
  coords::Coords *lhs_;
  coords::Coords *rhs_;
};


/*************
* PAREN EXPR
**************/

// Should hold coordinates of child expression
class VecParenExpr : public VecExpr {
  public:
  VecParenExpr(coords::VecExpr *expr);
  virtual std::string toString() const;

  coords::VecExpr* getExpr() const {
    return this->expr_;
  };

  bool operator==(const VecParenExpr &other) const {
    return this->state_ == other.state_;
  }
  protected:
    coords::VecExpr *expr_;
};

class ScalarParenExpr : public ScalarExpr {
  public:
  ScalarParenExpr(coords::ScalarExpr *expr);
  virtual std::string toString() const;

  coords::ScalarExpr* getExpr() const {
    return this->expr_;
  };

  bool operator==(const ScalarParenExpr &other) const {
    return this->state_ == other.state_;
  }
  protected:
    coords::ScalarExpr *expr_;
};

class TransformParenExpr : public TransformExpr {
  public:
  TransformParenExpr(coords::TransformExpr *expr);
  virtual std::string toString() const;

  coords::TransformExpr* getExpr() const {
    return this->expr_;
  };

  bool operator==(const TransformParenExpr &other) const {
    return this->state_ == other.state_;
  }
  protected:
    coords::TransformExpr *expr_;
};


/*******
* 
********/

enum VectorCtorType { VEC_CTOR_LIT, VEC_CTOR_EXPR, VEC_CTOR_VAR };
enum ScalarCtorType { FLOAT_CTOR_LIT, FLOAT_CTOR_EXPR, FLOAT_CTOR_VAR };
enum TransformCtorType {TRANSFORM_CTOR_LIT, TRANSFORM_CTOR_EXPR, TRANSFORM_CTOR_VAR};

// Superclass. Abstract
class Vector : public VecExpr {
public:
  Vector(coords::VectorCtorType tag);
  VectorCtorType getVectorType();
  virtual std::string toString() const;
  bool operator==(const Vector &other) const {
    return this->state_ == other.state_;
  }
protected:
  const VectorCtorType tag_;
};

class Scalar : public ScalarExpr {
public:
  Scalar(coords::ScalarCtorType tag);
  ScalarCtorType getScalarType();
  virtual std::string toString() const;
  bool operator==(const Scalar &other) const {
    return this->state_ == other.state_;
  }
protected:
  const ScalarCtorType tag_;
};

class Transform : public TransformExpr {
public:
  Transform(coords::TransformCtorType tag);
  TransformCtorType getTransformType();
  virtual std::string toString() const;
  bool operator==(const Transform &other) const {
    return this->state_ == other.state_;
  }
protected:
  const TransformCtorType tag_;
};

// TODO: methods to get x, y, z
class Vector_Lit : public Vector {
public:
  Vector_Lit();
  virtual std::string toString() const;
};

class Scalar_Lit : public Scalar {
public:
  Scalar_Lit();
  virtual std::string toString() const;
};

class Transform_Lit : public Transform {
public:
  Transform_Lit(coords::VecExpr* arg1, coords::VecExpr* arg2, coords::VecExpr* arg3);
  virtual std::string toString() const;
  coords::VecExpr* getVecArg1() const {return arg1_;};
  coords::VecExpr* getVecArg2() const {return arg2_;};
  coords::VecExpr* getVecArg3() const {return arg3_;};

private:
  coords::VecExpr *arg1_, *arg2_, *arg3_;
};


class Vector_Var : public Vector {
public:
  Vector_Var(coords::VecVarExpr *expr);
  virtual std::string toString() const;
  VecVarExpr *getVecVarExpr();
private:
  VecVarExpr *expr_;
};


class Scalar_Var : public Scalar {
public:
  Scalar_Var(coords::ScalarVarExpr *expr);
  virtual std::string toString() const;
  ScalarVarExpr *getScalarVarExpr();
private:
  ScalarVarExpr *expr_;
};


class Transform_Var : public Transform {
public:
  Transform_Var(coords::TransformVarExpr *expr);
  virtual std::string toString() const;
  TransformVarExpr *getTransformVarExpr();
private:
  TransformVarExpr *expr_;
};



// TODO: change name to VecVecAddExpr?
class Vector_Expr : public Vector {
public:
  Vector_Expr(coords::VecExpr *expr);
  virtual std::string toString() const;
  Vector_Expr *getVector_Expr();
private:
  VecExpr *expr_;
};


class Scalar_Expr : public Scalar {
public:
  Scalar_Expr(coords::ScalarExpr *expr);
  virtual std::string toString() const;
  Scalar_Expr *getScalar_Expr();
private:
  ScalarExpr *expr_;
};


class Transform_Expr : public Transform {
public:
  Transform_Expr(coords::TransformExpr *expr);
  virtual std::string toString() const;
  Transform_Expr *getTransform_Expr();
private:
  TransformExpr *expr_;
};

/****
 * Def
 ****/

class Vector_Def : public Coords {
public:
  Vector_Def(coords::VecIdent *id,
             coords::VecExpr *expr);
  coords::VecIdent *getIdent() const;
  coords::VecExpr *getExpr() const;
  virtual std::string toString() const;
  bool operator==(const Vector_Def &other) const {
    return this->state_ == other.state_;
  }
private:
  VecIdent *id_;
  VecExpr *expr_;
};

class Scalar_Def : public Coords {
public:
  Scalar_Def(coords::ScalarIdent *id,
             coords::ScalarExpr *expr);
  coords::ScalarIdent *getIdent() const;
  coords::ScalarExpr *getExpr() const;
  virtual std::string toString() const;
  bool operator==(const Scalar_Def &other) const {
    return this->state_ == other.state_;
  }
private:
  ScalarIdent *id_;
  ScalarExpr *expr_;
};

class Transform_Def : public Coords {
public:
  Transform_Def(coords::TransformIdent *id,
             coords::TransformExpr *expr);
  coords::TransformIdent *getIdent() const;
  coords::TransformExpr *getExpr() const;
  virtual std::string toString() const;
  bool operator==(const Transform_Def &other) const {
    return this->state_ == other.state_;
  }
private:
  TransformIdent *id_;
  TransformExpr *expr_;
};

class Vector_Assign : public Coords {
public:
  Vector_Assign(coords::VecVarExpr *id,
             coords::VecExpr *expr);
  coords::VecVarExpr *getVarExpr() const;
  coords::VecExpr *getExpr() const;
  virtual std::string toString() const;
  bool operator==(const Vector_Assign &other) const {
    return this->state_ == other.state_;
  }
private:
  VecVarExpr *id_;
  VecExpr *expr_;
};

class Scalar_Assign : public Coords {
public:
  Scalar_Assign(coords::ScalarVarExpr *id,
             coords::ScalarExpr *expr);
  coords::ScalarVarExpr *getVarExpr() const;
  coords::ScalarExpr *getExpr() const;
  virtual std::string toString() const;
  bool operator==(const Scalar_Assign &other) const {
    return this->state_ == other.state_;
  }
private:
  ScalarVarExpr *id_;
  ScalarExpr *expr_;
};

class Transform_Assign : public Coords {
public:
  Transform_Assign(coords::TransformVarExpr *id,
             coords::TransformExpr *expr);
  coords::TransformVarExpr *getVarExpr() const;
  coords::TransformExpr *getExpr() const;
  virtual std::string toString() const;
  bool operator==(const Transform_Assign &other) const {
    return this->state_ == other.state_;
  }
private:
  TransformVarExpr *id_;
  TransformExpr *expr_;
};

} // namespace coords

#endif