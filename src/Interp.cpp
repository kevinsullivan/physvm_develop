#include "Interp.h"

#include <g3log/g3log.hpp>

//using namespace g3; 

namespace interp {

Interp::Interp(coords::VecIdent* c, domain::VecIdent *d) 
  : type_(dom_vecIdent_type), coords_(c), ident_(d) {
}

Interp::Interp(coords::VecExpr *c, domain::VecExpr *d) 
  : type_(dom_vecExpr_type), coords_(c), expr_(d)  {
}

Interp::Interp(coords::Vector *c, domain::Vector *d)
  : type_(dom_vector_type), coords_(c), vector_(d) {

}

Interp::Interp(coords::Vector_Def *c, domain::Vector_Def *d) 
  : type_(dom_vector_def_type), coords_(c), def_(d) {
  
}
 
/******
 * Ident
 ******/

VecIdent::VecIdent(coords::VecIdent* c, domain::VecIdent* d) : Interp(c, d) {
}

std::string VecIdent::toString() const {
  std::cerr << "Need to implement interp::VecIdent::toString()\n";
}

  


/*****
 * Expr
 *****/

VecExpr::VecExpr(coords::VecExpr* c, domain::VecExpr* d) 
: Interp(c, d)  {}

std::string VecExpr::toString() const {}



VecVarExpr::VecVarExpr(coords::VecVarExpr* c, domain::VecVarExpr* d) : VecExpr(c, d) {}

std::string VecVarExpr::toString() const {}


VecVecAddExpr::VecVecAddExpr(coords::VecVecAddExpr* c, domain::VecVecAddExpr* d, 
                             interp::Interp *mem, interp::Interp *arg)  
  : VecExpr(c, d), mem_(mem), arg_(arg) {}
 
std::string VecVecAddExpr::toString() const {} 



 
Vector::Vector(coords::Vector* c, domain::Vector* d) : Interp(c, d) {}

std::string Vector::toString() const {}



Vector_Lit::Vector_Lit(coords::Vector_Lit* c, domain::Vector_Lit* d) : Vector(c,d) {

}

std::string Vector_Lit::toString() const {

}

Vector_Var::Vector_Var(coords::Vector_Var* c, domain::Vector_Var* d) : Vector(c,d) {

}

std::string Vector_Var::toString() const {

}

Vector_Expr::Vector_Expr(coords::Vector_Expr *c, domain::Vector_Expr* d) : Vector(c,d) {

}

std::string Vector_Expr::toString() const {

}


/****
 * Def
 ****/

Vector_Def::Vector_Def(coords::Vector_Def* c, domain::Vector_Def* d) : Interp(c,d) {

}
std::string Vector_Def::toString() const {

}

} // namespace coords
