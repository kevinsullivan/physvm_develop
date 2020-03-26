#include "Interp.h"

//#include <g3log/g3log.hpp>

//using namespace g3; 

namespace interp {

Interp::Interp(coords::VecIdent* c, domain::VecIdent *d) 
  : coords_(c), type_(dom_vecIdent_type), ident_(d) {
}

Interp::Interp(coords::VecExpr *c, domain::VecExpr *d) 
  : coords_(c), type_(dom_vecExpr_type), expr_(d)  {
}

Interp::Interp(coords::Vector *c, domain::Vector *d)
  : coords_(c), type_(dom_vector_type), vector_(d) {
}

Interp::Interp(coords::Vector_Def *c, domain::Vector_Def *d) 
  : coords_(c), type_(dom_vector_def_type), def_(d) {
}

Interp::Interp(coords::FloatIdent* c, domain::FloatIdent *d) 
  : coords_(c), type_(dom_floatIdent_type), float_ident_(d) {
}

Interp::Interp(coords::FloatExpr *c, domain::FloatExpr *d) 
  : coords_(c), type_(dom_floatExpr_type), float_expr_(d)  {
}

Interp::Interp(coords::Float *c, domain::Float *d)
  : coords_(c), type_(dom_float_type), float_(d) {
}

Interp::Interp(coords::Float_Def *c, domain::Float_Def *d) 
  : coords_(c), type_(dom_float_def_type), float_def_(d) {
}

/**********
 * Abstract
 **********/


std::string Interp::toString() const {
  //LOG(FATAL) << "Interp::toString: Error. Should not be called. Abstract.\n";
  return "";
}

/******
 * Ident
 ******/

VecIdent::VecIdent(coords::VecIdent* c, domain::VecIdent* d) : Interp(c,d) {
}

std::string VecIdent::toString() const {
  std::string ret = "";
//  ret += "( ";
  ret += coords_->toString();
  ret += " : peirce.vec ";
  ret += ident_->getSpaceContainer()->toString();
//  ret += " )";
  return ret;
}

FloatIdent::FloatIdent(coords::FloatIdent* c, domain::FloatIdent* d) : Interp(c,d) {
}

std::string FloatIdent::toString() const {
  std::string ret = "";
//  ret += "( ";
  ret += coords_->toString();
  ret += " : peirce.scalar ";
  ret += ident_->getSpaceContainer()->toString();
//  ret += " )";
  return ret;
}

/*****
 * Expr
 *****/

VecExpr::VecExpr(coords::VecExpr* c, domain::VecExpr* d)  : Interp(c, d)  {
}

std::string VecExpr::toString() const {
  //LOG(FATAL) << "Error. Call to abstract interp::VecIdent::toString().\n";
  return "Should not call abstract interp::VecExpr::toString().";
}

FloatExpr::FloatExpr(coords::FloatExpr* c, domain::FloatExpr* d)  : Interp(c, d)  {
}

std::string FloatExpr::toString() const {
  //LOG(FATAL) << "Error. Call to abstract interp::FloatIdent::toString().\n";
  return "Should not call abstract interp::FloatIdent::toString().";
}


VecVarExpr::VecVarExpr(coords::VecVarExpr* c, domain::VecVarExpr* d) : VecExpr(c, d) {
}

std::string VecVarExpr::toString() const {
  std::string ret = "";
  ret += "( ";
  ret += coords_->toString();
  ret += " : peirce.vec ";
  ret += expr_->getSpaceContainer()->toString(); 
  ret += " )";
  return ret;
}

FloatVarExpr::FloatVarExpr(coords::FloatVarExpr* c, domain::FloatVarExpr* d) :FloatExpr(c, d) {
}

std::string FloatVarExpr::toString() const {
  std::string ret = "";
  ret += "( ";
  ret += coords_->toString();
  ret += " : peirce.float ";
  ret += float_expr_->getSpaceContainer()->toString(); 
  ret += " )";
  return ret;
}



VecVecAddExpr::VecVecAddExpr(coords::VecVecAddExpr* c, domain::VecVecAddExpr* d, 
                             interp::Interp *mem, interp::Interp *arg)  
  : VecExpr(c, d), mem_(mem), arg_(arg) {
}

 
std::string VecVecAddExpr::toString() const {
  std::string ret = "";
  ret += "( peirce.add ";
  ret += mem_->toString();
  ret += " ";
  ret += arg_->toString();
  ret += " : peirce.vec ";
  ret += expr_->getSpaceContainer()->toString(); 
  ret += " )";
  return ret;  
} 

VecScalarMulExpr::VecScalarMulExpr(coords::VecScalarMulExpr* c, domain::VecScalarMulExpr* d, 
                             interp::Interp *vec, interp::Interp *flt)  
  : VecExpr(c, d), vec_(vec), flt_(flt) {
}

 
std::string VecScalarMulExpr::toString() const {
  std::string ret = "";
  ret += "( peirce.mul ";
  ret += vec_->toString();
  ret += " ";
  ret += flt_->toString();
  ret += " : peirce.vec ";
  ret += expr_->getSpaceContainer()->toString(); 
  ret += " )";
  return ret;  
} 

FloatFloatAddExpr::FloatFloatAddExpr(coords::FloatFloatAddExpr* c, domain::FloatFloatAddExpr* d, 
                             interp::Interp *lhs, interp::Interp *rhs)  
  : FloatExpr(c, d), lhs_(lhs), rhs_(rhs) {
}

 
std::string FloatFloatAddExpr::toString() const {
  std::string ret = "";
  ret += "( peirce.add ";
  ret += lhs_->toString();
  ret += " ";
  ret += rhs_->toString();
  ret += " : peirce.Float ";
  ret += expr_->getSpaceContainer()->toString(); 
  ret += " )";
  return ret;  
} 

FloatFloatMulExpr::FloatFloatMulExpr(coords::FloatFloatMulExpr* c, domain::FloatFloatMulExpr* d, 
                             interp::Interp *lhs, interp::Interp *rhs)  
  : FloatExpr(c, d), lhs_(lhs), rhs_(rhs) {
}

 
std::string FloatFloatMulExpr::toString() const {
  std::string ret = "";
  ret += "( peirce.mul ";
  ret += lhs_->toString();
  ret += " ";
  ret += rhs_->toString();
  ret += " : peirce.float ";
  ret += expr_->getSpaceContainer()->toString(); 
  ret += " )";
  return ret;  
} 

VecParenExpr::VecParenExpr
    (coords::VecParenExpr* c, domain::VecParenExpr* d, interp::VecExpr *e) 
    : VecExpr(c, d), paren_expr_(e) {
}

std::string VecParenExpr::toString() const {
  std::string ret = "";
  ret += "( ( ";
  ret += paren_expr_->toString();
  ret += " ) : peirce.vec ";

  // TODO: Abstract superclass data members
  ret += expr_->getSpaceContainer()->toString(); 

  ret += " )";
  return ret;  
} 


FloatParenExpr::FloatParenExpr
    (coords::FloatParenExpr* c, domain::FloatParenExpr* d, interp::FloatExpr *e) 
    : FloatExpr(c, d), paren_expr_(e) {
}

std::string FloatParenExpr::toString() const {
  std::string ret = "";
  ret += "( ( ";
  ret += paren_expr_->toString();
  ret += " ) : peirce.scalar ";

  // TODO: Abstract superclass data members
  ret += expr_->getSpaceContainer()->toString(); 

  ret += " )";
  return ret;  
} 




/*******
* Vector
********/
 
Vector::Vector(coords::Vector* c, domain::Vector* d) : Interp(c, d) {}

std::string Vector::toString() const {
  //LOG(INFO) << "Interp::Vector::toString().\n";
  return "A_Vector";
}
 
Float::Float(coords::Float* c, domain::Float* d) : Interp(c, d) {}

std::string Float::toString() const {
  //LOG(INFO) << "Interp::Vector::toString().\n";
  return "A_Float";
}

Vector_Lit::Vector_Lit(coords::Vector_Lit* c, domain::Vector_Lit* d) : Vector(c,d) {
}

std::string Vector_Lit::toString() const {
  std::string ret = "";
  ret += "( peirce.vec.mkVector ";
  ret += vector_->getSpaceContainer()->toString();
  ret += " ";
  ret += static_cast<coords::Vector_Lit *>(coords_)->toString();
  ret += " )";
  return ret;
}

Float_Lit::Float_Lit(coords::Float_Lit* c, domain::Float_Lit* d) : Float(c,d) {
}

std::string Float_Lit::toString() const {
  std::string ret = "";
  ret += "( peirce.vec.mkScalar ";
  ret += float_->getSpaceContainer()->toString();
  ret += " ";
  ret += static_cast<coords::Vector_Lit *>(coords_)->toString();
  ret += " )";
  return ret;
}

Vector_Var::Vector_Var(coords::Vector_Var* c, domain::Vector_Var* d) : Vector(c,d) {

}

std::string Vector_Var::toString() const {
  //LOG(FATAL) << "interp::Vector_Var::toString. Error. Not implemented.\n";
  return "";
}

Float_Var::Float_Var(coords::Float_Var* c, domain::Float_Var* d) : Float(c,d) {

}

std::string Float_Var::toString() const {
  //LOG(FATAL) << "interp::Vector_Var::toString. Error. Not implemented.\n";
  return "";
}

Vector_Expr::Vector_Expr(coords::Vector_Expr *c, domain::Vector_Expr* d, interp::VecExpr *expr_interp) 
  : Vector(c,d), expr_interp_(expr_interp) {

}

std::string Vector_Expr::toString() const {
  return getVector_Expr()->toString(); 
}


Float_Expr::Float_Expr(coords::Float_Expr *c, domain::Float_Expr* d, interp::FloatExpr *expr_interp) 
  : Float(c,d), expr_interp_(expr_interp) {

}

std::string Float_Expr::toString() const {
  return getFloat_Expr()->toString(); 
}


/****
 * Def
 ****/

Vector_Def::Vector_Def(coords::Vector_Def* c, domain::Vector_Def* d, interp::VecIdent *id, interp::Vector *vec) 
  : Interp(c,d), id_(id), vec_(vec) { 
}
std::string Vector_Def::toString() const {
  std::string ret = "def ";
  ret += id_->toString();
  ret += " := ";
  try{
    if(vec_)
      ret += vec_->toString(); 
  }
  catch(std::exception ex)
  {

  }
  return ret;
}

Float_Def::Float_Def(coords::Float_Def* c, domain::Float_Def* d, interp::FloatIdent *id, interp::Float *flt) 
  : Interp(c,d), id_(id), flt_(flt) { 
}
std::string Float_Def::toString() const {
  std::string ret = "def ";
  ret += id_->toString();
  ret += " := ";
  try{
    if(flt_)
      ret += flt_->toString(); 
  }
  catch(std::exception ex)
  {

  }
  return ret;
}

} // namespace coords
