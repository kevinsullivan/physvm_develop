#include "Interp.h"

#include <g3log/g3log.hpp>

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

/**********
 * Abstract
 **********/


std::string Interp::toString() const {
  LOG(FATAL) << "Interp::toString: Error. Should not be called. Abstract.\n";
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
  ret += ident_->getSpace()->toString();
//  ret += " )";
  return ret;
}

/*****
 * Expr
 *****/

VecExpr::VecExpr(coords::VecExpr* c, domain::VecExpr* d)  : Interp(c, d)  {
}

std::string VecExpr::toString() const {
  LOG(FATAL) << "Error. Call to abstract interp::VecIdent::toString().\n";
  return "Should not call abstract interp::VecIdent::toString().";
}

VecVarExpr::VecVarExpr(coords::VecVarExpr* c, domain::VecVarExpr* d) : VecExpr(c, d) {
}

std::string VecVarExpr::toString() const {
  std::string ret = "";
  ret += "( ";
  ret += coords_->toString();
  ret += " : peirce.vec ";
  ret += expr_->getSpace()->toString(); 
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
  ret += expr_->getSpace()->toString(); 
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
  ret += expr_->getSpace()->toString(); 

  ret += " )";
  return ret;  
} 



/*******
* Vector
********/
 
Vector::Vector(coords::Vector* c, domain::Vector* d) : Interp(c, d) {}

std::string Vector::toString() const {
  LOG(INFO) << "Interp::Vector::toString().\n";
  return "A_Vector";
}


Vector_Lit::Vector_Lit(coords::Vector_Lit* c, domain::Vector_Lit* d) : Vector(c,d) {
}

std::string Vector_Lit::toString() const {
  std::string ret = "";
  ret += "( peirce.vec.mkVector ";
  ret += vector_->getSpace()->getName();
  ret += " ";
  ret += static_cast<coords::Vector_Lit *>(coords_)->toString();
  ret += " )";
  return ret;
}

Vector_Var::Vector_Var(coords::Vector_Var* c, domain::Vector_Var* d) : Vector(c,d) {

}

std::string Vector_Var::toString() const {
  LOG(FATAL) << "interp::Vector_Var::toString. Error. Not implemented.\n";
  return "";
}


Vector_Expr::Vector_Expr(coords::Vector_Expr *c, domain::Vector_Expr* d, interp::VecExpr *expr_interp) 
  : Vector(c,d), expr_interp_(expr_interp) {

}

std::string Vector_Expr::toString() const {
  return getVector_Expr()->toString(); 
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

} // namespace coords
