/*
Establish interpretations for AST nodes:

-  get any required information from oracle 
-  create coordinates for object
-  update ast-coord bijections
-  create corresponding domain object
-  update coord-domain bijection
-  create element-wise inter object
-  update maps: coords-interp, interp-domain
*/

// TODO: These two can be integrated
#include "Coords.h"
#include "Interpretation.h"
#include "Interp.h"
#include "CoordsToInterp.h"
#include "CoordsToDomain.h"
#include "InterpToDomain.h"
#include "ASTToCoords.h"
#include "Oracle_AskAll.h"    // default oracle

//#include <g3log/g3log.hpp>

using namespace interp;

Interpretation::Interpretation() { 
    domain_ = new domain::Domain();
    oracle_ = new oracle::Oracle_AskAll(domain_); 
    /* 
    context_ can only be set later, once Clang starts parse
    */
    ast2coords_ = new ast2coords::ASTToCoords(); 
    coords2dom_ = new coords2domain::CoordsToDomain();
    coords2interp_ = new coords2interp::CoordsToInterp();
    interp2domain_ = new interp2domain::InterpToDomain();
}

/******
* Ident
******/

void Interpretation::mkVecIdent(ast::VecIdent *ast)
{
  coords::VecIdent *coords = ast2coords_->mkVecIdent(ast, context_);
  //LOG(DEBUG) << "Interpretation::mkVecIdent. ast=" << std::hex << ast << ", " << coords->toString() << "\n";
  //domain::Space &space = oracle_->getSpaceForVecIdent(coords);
  domain::VecIdent *dom = domain_->mkVecIdent();
  coords2dom_->putVecIdent(coords, dom);
  interp::VecIdent *interp = new interp::VecIdent(coords, dom);
  coords2interp_->putVecIdent(coords, interp);
  interp2domain_->putVecIdent(interp, dom);
}

void Interpretation::mkFloatIdent(ast::FloatIdent *ast)
{
  coords::FloatIdent *coords = ast2coords_->mkFloatIdent(ast, context_);
  //LOG(DEBUG) << "Interpretation::mkVecIdent. ast=" << std::hex << ast << ", " << coords->toString() << "\n";
  //domain::Space &space = oracle_->getSpaceForVecIdent(coords);
  domain::FloatIdent *dom = domain_->mkFloatIdent();
  coords2dom_->putFloatIdent(coords, dom);
  interp::FloatIdent *interp = new interp::FloatIdent(coords, dom);
  coords2interp_->putFloatIdent(coords, interp);
  interp2domain_->putFloatIdent(interp, dom);
}

/*****
* Expr
*****/


void Interpretation::mkVecVarExpr(ast::VecVarExpr *ast/*, clang::ASTContext *c*/) {
    coords::VecVarExpr *coords = ast2coords_->mkVecVarExpr(ast, context_);
    //LOG(DEBUG) << "Interpretation::mkVecVarExpr. ast=" << std::hex << ast << ", " << coords->toString() << "\n";
    //ast->dump();
    //domain::Space &space = oracle_->getSpaceForVecVarExpr(coords);
    domain::VecVarExpr *dom = domain_->mkVecVarExpr();
    coords2dom_->PutVecVarExpr(coords, dom);
    interp::VecVarExpr *interp = new interp::VecVarExpr(coords,dom);
    coords2interp_->putVecVarExpr(coords, interp);
    interp2domain_->putVecVarExpr(interp,dom);
}

void Interpretation::mkFloatVarExpr(ast::FloatVarExpr *ast/*, clang::ASTContext *c*/) {
    coords::FloatVarExpr *coords = ast2coords_->mkFloatVarExpr(ast, context_);
    //LOG(DEBUG) << "Interpretation::mkVecVarExpr. ast=" << std::hex << ast << ", " << coords->toString() << "\n";
    //ast->dump();
    //domain::Space &space = oracle_->getSpaceForVecVarExpr(coords);
    domain::FloatVarExpr *dom = domain_->mkFloatVarExpr();
    coords2dom_->PutFloatVarExpr(coords, dom);
    interp::FloatVarExpr *interp = new interp::FloatVarExpr(coords,dom);
    coords2interp_->putFloatVarExpr(coords, interp);
    interp2domain_->putFloatVarExpr(interp,dom);
}

void Interpretation::mkVecVecAddExpr(ast::VecVecAddExpr *add_ast, const ast::VecExpr *mem_expr, const ast::VecExpr *arg_expr) {
  coords::VecExpr *mem_coords = static_cast<coords::VecExpr*>
                                  (ast2coords_->getStmtCoords(mem_expr));
  coords::VecExpr *arg_coords = static_cast<coords::VecExpr*>
                                  (ast2coords_->getStmtCoords(arg_expr));
  //LOG(DEBUG) << "Interpretation::mkVecVecAddExpr. ast=" << std::hex << add_ast << "\n";
  if (mem_coords == NULL || arg_coords == NULL) {
    //LOG(FATAL) <<"Interpretation::mkVecVecAddExpr: bad coordinates. Mem coords "
    //        << std::hex << mem_coords << " arg coords "
    //        << std::hex << arg_coords << "\n";
  }
  coords::VecVecAddExpr *coords = ast2coords_->mkVecVecAddExpr(add_ast, context_, mem_coords, arg_coords);
  //domain::Space &space = oracle_->getSpaceForAddExpression(mem_coords, arg_coords);
  domain::VecExpr *dom_mem_expr = coords2dom_->getVecExpr(mem_coords);
  domain::VecExpr *dom_arg_expr = coords2dom_->getVecExpr(arg_coords);
  if (dom_mem_expr == NULL || dom_arg_expr == NULL) {
    //LOG(DEBUG) <<"Interpretation::mkVecVecAddExpr: bad domain exprs. Mem "
    //          << std::hex << dom_mem_expr << " Arg "
    //          << std::hex << dom_arg_expr << "\n";
  }
  domain::VecVecAddExpr *dom = domain_->mkVecVecAddExpr(dom_mem_expr, dom_arg_expr);
  coords2dom_->PutVecVecAddExpr(coords, dom);
  //LOG(DEBUG) << "Interpretation::mkVecVecAddExpr: Mem_Coords: " << mem_coords->toString() << "\n";
  //LOG(DEBUG) << "Interpretation::mkVecVecAddExpr: Arg_Coords: " << arg_coords->toString() << "\n";

  interp::Interp *mem_interp = coords2interp_->getVecExpr(mem_coords);  // dyn type's toString not being called
  std::string mi_str = mem_interp->toString();
  //LOG(DEBUG) << "Interpretation::mkVecVecAddExpr: Mem_Interp: " << mi_str << "\n";
  interp::Interp *arg_interp = coords2interp_->getVecExpr(arg_coords);
  //LOG(DEBUG) << "Interpretation::mkVecVecAddExpr: Arg_Interp: " << arg_interp->toString() << "\n";
  interp::VecVecAddExpr *interp = new interp::VecVecAddExpr(coords, dom, mem_interp, arg_interp);
  coords2interp_->putVecVecAddExpr(coords, interp); 
  interp2domain_->putVecVecAddExpr(interp,dom);
}

void Interpretation::mkVecScalarMulExpr(ast::VecScalarMulExpr *mul_ast, const ast::VecExpr *vec_expr, const ast::FloatExpr *flt_expr) {
  coords::FloatExpr *flt_coords = static_cast<coords::FloatExpr*>
                                  (ast2coords_->getStmtCoords(flt_expr));
  coords::VecExpr *vec_coords = static_cast<coords::VecExpr*>
                                  (ast2coords_->getStmtCoords(vec_expr));
  //LOG(DEBUG) << "Interpretation::mkVecVecAddExpr. ast=" << std::hex << add_ast << "\n";
  if (flt_coords == NULL || vec_coords == NULL) {
    //LOG(FATAL) <<"Interpretation::mkVecVecAddExpr: bad coordinates. Mem coords "
    //        << std::hex << mem_coords << " arg coords "
    //        << std::hex << arg_coords << "\n";
  }
  coords::VecScalarMulExpr *coords = ast2coords_->mkVecScalarMulExpr(mul_ast, context_, flt_coords, vec_coords);
  //domain::Space &space = oracle_->getSpaceForAddExpression(mem_coords, arg_coords);
  domain::FloatExpr *dom_flt_expr = coords2dom_->getFloatExpr(flt_coords);
  domain::VecExpr *dom_vec_expr = coords2dom_->getVecExpr(vec_coords);
  if (dom_flt_expr == NULL || dom_vec_expr == NULL) {
    //LOG(DEBUG) <<"Interpretation::mkVecVecAddExpr: bad domain exprs. Mem "
    //          << std::hex << dom_mem_expr << " Arg "
    //          << std::hex << dom_arg_expr << "\n";
  }
  domain::VecScalarMulExpr *dom = domain_->mkVecScalarMulExpr(dom_vec_expr, dom_flt_expr);
  coords2dom_->PutVecScalarMulExpr(coords, dom);
  //LOG(DEBUG) << "Interpretation::mkVecVecAddExpr: Mem_Coords: " << mem_coords->toString() << "\n";
  //LOG(DEBUG) << "Interpretation::mkVecVecAddExpr: Arg_Coords: " << arg_coords->toString() << "\n";

  interp::Interp *flt_interp = coords2interp_->getFloatExpr(flt_coords);  // dyn type's toString not being called
  std::string mi_str = flt_interp->toString();
  //LOG(DEBUG) << "Interpretation::mkVecVecAddExpr: Mem_Interp: " << mi_str << "\n";
  interp::Interp *vec_interp = coords2interp_->getVecExpr(vec_coords);
  //LOG(DEBUG) << "Interpretation::mkVecVecAddExpr: Arg_Interp: " << arg_interp->toString() << "\n";
  interp::VecScalarMulExpr *interp = new interp::VecScalarMulExpr(coords, dom, flt_interp, vec_interp);
  coords2interp_->putVecScalarMulExpr(coords, interp); 
  interp2domain_->putVecScalarMulExpr(interp,dom);
}

void Interpretation::mkVecParenExpr(ast::VecParenExpr *ast, ast::VecExpr *expr) { 
    coords::VecParenExpr *coords = ast2coords_->mkVecParenExpr(ast, context_, expr);   
    coords::VecExpr *expr_coords = static_cast<coords::VecExpr *>(ast2coords_->getStmtCoords(expr));
    //LOG(DEBUG) << 
    //  "Interpretation::mkVecParenExpr. ast=" << 
    //  std::hex << ast << ", " << coords->toString() << 
    //  "expr = " << expr_coords->toString() << "\n";
    //domain::Space &space = oracle_->getSpaceForVecParenExpr(coords);
    domain::VecExpr *dom_expr = coords2dom_->getVecExpr(expr_coords);
    domain::VecParenExpr *dom = domain_->mkVecParenExpr(dom_expr);
    coords2dom_->PutVecParenExpr(coords, dom);
    interp::VecExpr *expr_interp = coords2interp_->getVecExpr(expr_coords);
    interp::VecParenExpr *interp = new interp::VecParenExpr(coords, dom, expr_interp);
    coords2interp_->putVecParenExpr(coords, interp);  
    interp2domain_->putVecParenExpr(interp,dom);
} 

void Interpretation::mkFloatParenExpr(ast::FloatParenExpr *ast, ast::FloatExpr *expr) { 
    coords::FloatParenExpr *coords = ast2coords_->mkFloatParenExpr(ast, context_, expr);   
    coords::FloatExpr *expr_coords = static_cast<coords::FloatExpr *>(ast2coords_->getStmtCoords(expr));
    //LOG(DEBUG) << 
    //  "Interpretation::mkVecParenExpr. ast=" << 
    //  std::hex << ast << ", " << coords->toString() << 
    //  "expr = " << expr_coords->toString() << "\n";
    //domain::Space &space = oracle_->getSpaceForVecParenExpr(coords);
    domain::FloatExpr *dom_expr = coords2dom_->getFloatExpr(expr_coords);
    domain::FloatParenExpr *dom = domain_->mkFloatParenExpr(dom_expr);
    coords2dom_->PutFloatParenExpr(coords, dom);
    interp::FloatExpr *expr_interp = coords2interp_->getFloatExpr(expr_coords);
    interp::FloatParenExpr *interp = new interp::FloatParenExpr(coords, dom, expr_interp);
    coords2interp_->putFloatParenExpr(coords, interp);  
    interp2domain_->putFloatParenExpr(interp,dom);
} 
/*

    void mkFloatFloatAddExpr(ast::FloatFloatAddExpr *ast, const ast::FloatExpr *lhs, const ast::FloatExpr *rhs);
    void mkFloatFloarMulExpr(ast::FloatFloatMulExpr *ast, const ast::FloatExpr *lhs, const ast::FloatExpr *rhs);

*/
void Interpretation::mkFloatFloatAddExpr(ast::FloatFloatAddExpr *ast, const ast::FloatExpr* lhs, const ast::FloatExpr *rhs){
  coords::FloatExpr *lhs_coords = static_cast<coords::FloatExpr*>
                                  (ast2coords_->getStmtCoords(lhs));
  coords::FloatExpr *rhs_coords = static_cast<coords::FloatExpr*>
                                  (ast2coords_->getStmtCoords(rhs));
  //LOG(DEBUG) << "Interpretation::mkFloatFloatAddExpr. ast=" << std::hex << add_ast << "\n";
  if (lhs_coords == NULL || rhs_coords == NULL) {
    //LOG(FATAL) <<"Interpretation::mkFloatFloatAddExpr: bad coordinates. Mem coords "
    //        << std::hex << mem_coords << " arg coords "
    //        << std::hex << arg_coords << "\n";
  }
  coords::FloatFloatAddExpr *coords = ast2coords_->mkFloatFloatAddExpr(ast, context_, lhs_coords, rhs_coords);
  //domain::Space &space = oracle_->getSpaceForAddExpression(mem_coords, arg_coords);
  domain::FloatExpr *dom_lhs_expr = coords2dom_->getFloatExpr(lhs_coords);
  domain::FloatExpr *dom_rhs_expr = coords2dom_->getFloatExpr(rhs_coords);
  if (dom_lhs_expr == NULL || dom_rhs_expr == NULL) {
    //LOG(DEBUG) <<"Interpretation::mkFloatFloatAddExpr: bad domain exprs. Mem "
    //          << std::hex << dom_mem_expr << " Arg "
    //          << std::hex << dom_arg_expr << "\n";
  }
  domain::FloatFloatAddExpr *dom = domain_->mkFloatFloatAddExpr(dom_lhs_expr, dom_rhs_expr);
  coords2dom_->PutFloatFloatAddExpr(coords, dom);
  //LOG(DEBUG) << "Interpretation::mkFloatFloatAddExpr: Mem_Coords: " << mem_coords->toString() << "\n";
  //LOG(DEBUG) << "Interpretation::mkFloatFloatAddExpr: Arg_Coords: " << arg_coords->toString() << "\n";

  interp::Interp *lhs_interp = coords2interp_->getFloatExpr(lhs_coords);  // dyn type's toString not being called
  std::string mi_str = lhs_interp->toString();
  //LOG(DEBUG) << "Interpretation::mkFloatFloatAddExpr: Mem_Interp: " << mi_str << "\n";
  interp::Interp *rhs_interp = coords2interp_->getFloatExpr(rhs_coords);
  //LOG(DEBUG) << "Interpretation::mkFloatFloatAddExpr: Arg_Interp: " << arg_interp->toString() << "\n";
  interp::FloatFloatAddExpr *interp = new interp::FloatFloatAddExpr(coords, dom, lhs_interp, rhs_interp);
  coords2interp_->putFloatFloatAddExpr(coords, interp); 
  interp2domain_->putFloatFloatAddExpr(interp,dom);
}

void Interpretation::mkFloatFloatMulExpr(ast::FloatFloatMulExpr *ast, const ast::FloatExpr* lhs, const ast::FloatExpr *rhs){
  coords::FloatExpr *lhs_coords = static_cast<coords::FloatExpr*>
                                  (ast2coords_->getStmtCoords(lhs));
  coords::FloatExpr *rhs_coords = static_cast<coords::FloatExpr*>
                                  (ast2coords_->getStmtCoords(rhs));
  //LOG(DEBUG) << "Interpretation::mkFloatFloatMulExpr. ast=" << std::hex << Mul_ast << "\n";
  if (lhs_coords == NULL || rhs_coords == NULL) {
    //LOG(FATAL) <<"Interpretation::mkFloatFloatMulExpr: bad coordinates. lhs coords "
    //        << std::hex << lhs_coords << " rhs coords "
    //        << std::hex << rhs_coords << "\n";
  }
  coords::FloatFloatMulExpr *coords = ast2coords_->mkFloatFloatMulExpr(ast, context_, lhs_coords, rhs_coords);
  //domain::Space &space = oracle_->getSpaceForMulExpression(lhs_coords, rhs_coords);
  domain::FloatExpr *dom_lhs_expr = coords2dom_->getFloatExpr(lhs_coords);
  domain::FloatExpr *dom_rhs_expr = coords2dom_->getFloatExpr(rhs_coords);
  if (dom_lhs_expr == NULL || dom_rhs_expr == NULL) {
    //LOG(DEBUG) <<"Interpretation::mkFloatFloatMulExpr: bad domain exprs. lhs "
    //          << std::hex << dom_lhs_expr << " rhs "
    //          << std::hex << dom_rhs_expr << "\n";
  }
  domain::FloatFloatMulExpr *dom = domain_->mkFloatFloatMulExpr(dom_lhs_expr, dom_rhs_expr);
  coords2dom_->PutFloatFloatMulExpr(coords, dom);
  //LOG(DEBUG) << "Interpretation::mkFloatFloatMulExpr: lhs_Coords: " << lhs_coords->toString() << "\n";
  //LOG(DEBUG) << "Interpretation::mkFloatFloatMulExpr: rhs_Coords: " << rhs_coords->toString() << "\n";

  interp::Interp *lhs_interp = coords2interp_->getFloatExpr(lhs_coords);  // dyn type's toString not being called
  std::string mi_str = lhs_interp->toString();
  //LOG(DEBUG) << "Interpretation::mkFloatFloatMulExpr: lhs_Interp: " << mi_str << "\n";
  interp::Interp *rhs_interp = coords2interp_->getFloatExpr(rhs_coords);
  //LOG(DEBUG) << "Interpretation::mkFloatFloatMulExpr: rhs_Interp: " << rhs_interp->toString() << "\n";
  interp::FloatFloatMulExpr *interp = new interp::FloatFloatMulExpr(coords, dom, lhs_interp, rhs_interp);
  coords2interp_->putFloatFloatMulExpr(coords, interp); 
  interp2domain_->putFloatFloatMulExpr(interp,dom);
}

/*******
* Vector
*******/

/*
Vectors are fully "constructed" objects. We're seeing a bit of Clang AST
design showing through here, as clang separated things like function appl
expressions and objects constructed from them.
*/

void Interpretation::mkVector_Lit(ast::Vector_Lit *ast, float x, float y, float z) {
    coords::Vector_Lit *coords = ast2coords_->mkVector_Lit(ast, context_, x, y, z);  
    //domain::Space& s = oracle_->getSpaceForVector_Lit(coords);  //*new domain::Space("Interpretation::mkVector_Expr:: Warning. Using Stub Space\n.");
    domain::Vector_Lit *dom = domain_->mkVector_Lit(x, y, z);
    coords2dom_->putVector_Lit(coords, dom); 
    interp::Vector_Lit *interp = new interp::Vector_Lit(coords, dom);
    coords2interp_->putVector_Lit(coords, interp);
    interp2domain_->putVector_Lit(interp,dom);
}

void Interpretation::mkFloat_Lit(ast::Float_Lit *ast, float scalar) {
    coords::Float_Lit *coords = ast2coords_->mkFloat_Lit(ast, context_, scalar);  
    //domain::Space& s = oracle_->getSpaceForVector_Lit(coords);  //*new domain::Space("Interpretation::mkVector_Expr:: Warning. Using Stub Space\n.");
    domain::Float_Lit *dom = domain_->mkFloat_Lit(scalar);
    coords2dom_->putFloat_Lit(coords, dom); 
    interp::Float_Lit *interp = new interp::Float_Lit(coords, dom);
    coords2interp_->putFloat_Lit(coords, interp);
    interp2domain_->putFloat_Lit(interp,dom);
}

void Interpretation::mkVector_Expr(
      ast::Vector_Expr *ctor_ast, ast::VecExpr* expr_ast/*, clang::ASTContext *c*/) {
    coords::Vector_Expr *ctor_coords = ast2coords_->mkVector_Expr(ctor_ast, context_, expr_ast);
    coords::VecExpr *expr_coords = static_cast<coords::VecExpr *>(ast2coords_->getStmtCoords(expr_ast));
    //domain::Space& s = oracle_->getSpaceForVector_Expr(expr_coords);  //*new domain::Space("Interpretation::mkVector_Expr:: Warning. Using Stub Space\n.");
    domain::VecExpr *expr_dom = coords2dom_->getVecExpr(expr_coords);
    domain::Vector_Expr *dom_vec = domain_->mkVector_Expr(expr_dom); 
    coords2dom_->putVector_Expr(ctor_coords, dom_vec);
    interp::VecExpr *expr_interp = coords2interp_->getVecExpr(expr_coords);
    interp::Vector_Expr *interp = new interp::Vector_Expr(ctor_coords, dom_vec, expr_interp);
    coords2interp_->putVector_Expr(ctor_coords, interp);
    interp2domain_->putVector_Expr(interp, dom_vec);
}

void Interpretation::mkFloat_Expr(
      ast::Float_Expr *ctor_ast, ast::FloatExpr* expr_ast/*, clang::ASTContext *c*/) {
    coords::Float_Expr *ctor_coords = ast2coords_->mkFloat_Expr(ctor_ast, context_, expr_ast);
    coords::FloatExpr *expr_coords = static_cast<coords::FloatExpr *>(ast2coords_->getStmtCoords(expr_ast));
    //domain::Space& s = oracle_->getSpaceForVector_Expr(expr_coords);  //*new domain::Space("Interpretation::mkVector_Expr:: Warning. Using Stub Space\n.");
    domain::FloatExpr *expr_dom = coords2dom_->getFloatExpr(expr_coords);
    domain::Float_Expr *dom_flt = domain_->mkFloat_Expr(expr_dom); 
    coords2dom_->putFloat_Expr(ctor_coords, dom_flt);
    interp::FloatExpr *expr_interp = coords2interp_->getFloatExpr(expr_coords);
    interp::Float_Expr *interp = new interp::Float_Expr(ctor_coords, dom_flt, expr_interp);
    coords2interp_->putFloat_Expr(ctor_coords, interp);
    interp2domain_->putFloat_Expr(interp, dom_flt);
}

/****
* Def
*****/

/****
 * Note: Have made decision that main communicates with Interpretation in terms
 * of coords objects alone, not in terms of interp, oracle, or domain objects.
 * */

void Interpretation::mkVector_Def(ast::Vector_Def *def_ast,  
                                  ast::VecIdent *id_ast, 
                                  ast::VecExpr *expr_ast)
{
    coords::VecIdent *id_coords = static_cast<coords::VecIdent *>
      (ast2coords_->getDeclCoords(id_ast));
    coords::Vector *vec_coords = static_cast<coords::Vector *>
      (ast2coords_->getStmtCoords(expr_ast));
    coords::Vector_Def *def_coords = ast2coords_->mkVector_Def(def_ast, context_, id_coords, vec_coords);
    domain::VecIdent *vec_ident = coords2dom_->getVecIdent(id_coords);
    /*
    Here there is some subtlety. We don't know if what was left in our
    interpretation by previous work was a Vector_Lit or a Vector_Expr.
    So we check first for a Vector_Expr
    */
    domain::Vector *vec = coords2dom_->getVector(vec_coords);
    domain::Vector_Def* dom_vec_def = 
      domain_->mkVector_Def(vec_ident, vec); 
    coords2dom_->putVector_Def(def_coords, dom_vec_def);
    interp::VecIdent *id_interp = coords2interp_->getVecIdent(id_coords);
    interp::Vector *vec_interp = coords2interp_->getVector(vec_coords);
    interp::Vector_Def *interp = new interp::Vector_Def(def_coords, dom_vec_def, id_interp, vec_interp);
    coords2interp_->putVector_Def(def_coords, interp);
    interp2domain_->putVector_Def(interp, dom_vec_def);
}

void Interpretation::mkVector_Assign(ast::Vector_Assign *assign_ast,  
                                  ast::VecVarExpr *id_ast, 
                                  ast::VecExpr *expr_ast)
{
    coords::VecVarExpr *var_coords = static_cast<coords::VecVarExpr *>
      (ast2coords_->getStmtCoords(id_ast));
    coords::Vector *vec_coords = static_cast<coords::Vector *>
      (ast2coords_->getStmtCoords(expr_ast));
    coords::Vector_Assign *assign_coords = ast2coords_->mkVector_Assign(assign_ast, context_, var_coords, vec_coords);
    domain::VecVarExpr *vec_varexpr = coords2dom_->getVecVarExpr(var_coords);
    /*
    Here there is some subtlety. We don't know if what was left in our
    interpretation by previous work was a Vector_Lit or a Vector_Expr.
    So we check first for a Vector_Expr
    */
    domain::Vector *vec = coords2dom_->getVector(vec_coords);
    domain::Vector_Assign* dom_vec_assign = 
      domain_->mkVector_Assign(vec_varexpr, vec); 
    coords2dom_->putVector_Assign(assign_coords, dom_vec_assign);
    interp::VecVarExpr *var_interp = coords2interp_->getVecVarExpr(var_coords);
    interp::VecExpr *vec_interp = coords2interp_->getVecExpr(vec_coords);
    //std::cout<<vec_interp->toString()<<std::endl;
    interp::Vector_Assign *interp = new interp::Vector_Assign(assign_coords, dom_vec_assign, var_interp, vec_interp);
    coords2interp_->putVector_Assign(assign_coords, interp);
    interp2domain_->putVector_Assign(interp, dom_vec_assign);
}


void Interpretation::mkFloat_Def(ast::Float_Def *def_ast,  
                                  ast::FloatIdent *id_ast, 
                                  ast::FloatExpr *expr_ast)
{
    coords::FloatIdent *id_coords = static_cast<coords::FloatIdent *>
      (ast2coords_->getDeclCoords(id_ast));
    coords::Float *flt_coords = static_cast<coords::Float *>
      (ast2coords_->getStmtCoords(expr_ast));
    coords::Float_Def *def_coords = ast2coords_->mkFloat_Def(def_ast, context_, id_coords, flt_coords);
    domain::FloatIdent *flt_ident = coords2dom_->getFloatIdent(id_coords);
    /*
    Here there is some subtlety. We don't know if what was left in our
    interpretation by previous work was a Vector_Lit or a Vector_Expr.
    So we check first for a Vector_Expr
    */
    domain::Float *flt = coords2dom_->getFloat(flt_coords);
    domain::Float_Def* dom_flt_def = 
      domain_->mkFloat_Def(flt_ident, flt); 
    coords2dom_->putFloat_Def(def_coords, dom_flt_def);
    interp::FloatIdent *id_interp = coords2interp_->getFloatIdent(id_coords);
    interp::Float *flt_interp = coords2interp_->getFloat(flt_coords);
    interp::Float_Def *interp = new interp::Float_Def(def_coords, dom_flt_def, id_interp, flt_interp);
    coords2interp_->putFloat_Def(def_coords, interp);
    interp2domain_->putFloat_Def(interp, dom_flt_def);
}



void Interpretation::mkFloat_Assign(ast::Float_Assign *assign_ast,  
                                  ast::FloatVarExpr *id_ast, 
                                  ast::FloatExpr *expr_ast)
{
    coords::FloatVarExpr *id_coords = static_cast<coords::FloatVarExpr *>
      (ast2coords_->getStmtCoords(id_ast));
    coords::Float *float_coords = static_cast<coords::Float *>
      (ast2coords_->getStmtCoords(expr_ast));
    coords::Float_Assign *assign_coords = ast2coords_->mkFloat_Assign(assign_ast, context_, id_coords, float_coords);
    domain::FloatVarExpr *float_varexpr = coords2dom_->getFloatVarExpr(id_coords);
    /*
    Here there is some subtlety. We don't know if what was left in our
    interpretation by previous work was a Float_Lit or a Float_Expr.
    So we check first for a Float_Expr
    */
    domain::Float *Float = coords2dom_->getFloat(float_coords);
    domain::Float_Assign* dom_float_assign = 
      domain_->mkFloat_Assign(float_varexpr, Float); 
    coords2dom_->putFloat_Assign(assign_coords, dom_float_assign);
    interp::FloatVarExpr *id_interp = coords2interp_->getFloatVarExpr(id_coords);
    interp::FloatExpr *float_interp = coords2interp_->getFloatExpr(float_coords);
    interp::Float_Assign *interp = new interp::Float_Assign(assign_coords, dom_float_assign, id_interp, float_interp);
    coords2interp_->putFloat_Assign(assign_coords, interp);
    interp2domain_->putFloat_Assign(interp, dom_float_assign);
}

// private
// Precondition: coords2domain_ is defined for exp
//
domain::VecExpr* Interpretation::getVecExpr(ast::VecExpr* ast) {
    // we use these objects as key for query purposes
    coords::VecExpr *coords = 
        static_cast<coords::VecExpr *>(ast2coords_->getStmtCoords(ast));
    domain::VecExpr* dom = coords2dom_->getVecExpr(coords);
    if (!dom) {
       // LOG(DEBUG) <<"Interpretation::getVecExpr. Error. Undefined for key!\n";
    }
    return dom;
}

domain::FloatExpr* Interpretation::getFloatExpr(ast::FloatExpr* ast) {
    // we use these objects as key for query purposes
    coords::FloatExpr *coords = 
        static_cast<coords::FloatExpr *>(ast2coords_->getStmtCoords(ast));
    domain::FloatExpr* dom = coords2dom_->getFloatExpr(coords);
    if (!dom) {
       // LOG(DEBUG) <<"Interpretation::getVecExpr. Error. Undefined for key!\n";
    }
    return dom;
}

/******
 * 
 * TODO: Replace all this with direct calls to interp objects
 * TODO: Move checker-specific unparsing to separate client class.
 * ****/

// private
std::string Interpretation::toString_Spaces() {
  int index = 0;
  std::string retval = "";
  std::vector<domain::Space *> &s = domain_->getSpaces();
  for (std::vector<domain::Space *>::iterator it = s.begin(); it != s.end(); ++it)
    retval = retval.append("def ")
                 .append((*it)->toString()) 
                 .append(" : peirce.space := peirce.space.mk ")
                 .append(std::to_string(index++)) 
                 .append("\n");
  return retval;
}

// TODO: Private
//
std::string Interpretation::toString_Idents() {
    std::string retval = "";
    std::vector<domain::VecIdent*> &id = domain_->getVecIdents();
    for (std::vector<domain::VecIdent *>::iterator it = id.begin(); it != id.end(); ++it) {
        coords::VecIdent* coords = coords2dom_->getVecIdent(*it);
        interp::VecIdent *interp = coords2interp_->getVecIdent(coords);
        retval = retval.append(interp->toString());
        retval = retval.append("\n"); 
    }
    return retval;
}

// TODO: Factor toPrint (printing) out of coords, put here in, or in client of, interpretation
//
std::string Interpretation::toString_Exprs() {
  std::string retval = "";
  std::vector<domain::VecExpr*> &id = domain_->getVecExprs();
  for (std::vector<domain::VecExpr *>::iterator it = id.begin(); it != id.end(); ++it) {
      coords::VecExpr* coords = coords2dom_->getVecExpr(*it);
      interp::VecExpr *interp = coords2interp_->getVecExpr(coords);
      retval = retval.append(interp->toString());
      retval = retval.append("\n");
  }
  return retval;
}

std::string Interpretation::toString_Vectors() {
  std::string retval = "";
  std::vector<domain::Vector*> &id = domain_->getVectors();
  for (std::vector<domain::Vector *>::iterator it = id.begin(); it != id.end(); ++it) {
      coords::Vector* coords = coords2dom_->getVector(*it);
      interp::Vector *interp = coords2interp_->getVector(coords);   
      retval = retval
      .append("(")
      .append(interp->toString())
      .append(" : vec ")
      .append((*it)->getSpaceContainer()->toString())
      .append(")\n");
  }
  return retval;
}

std::string Interpretation::toString_Defs() {
  std::string retval = "";
  std::vector<domain::Vector_Def*> &id = domain_->getVectorDefs();
  for (std::vector<domain::Vector_Def *>::iterator it = id.begin(); it != id.end(); ++it) {
      coords::Vector_Def* coords = coords2dom_->getVector_Def(*it);
      interp::Vector_Def *interp = coords2interp_->getVector_Def(coords);
      retval = retval.append(interp->toString()).append("\n");
  }
  return retval;
}

std::string Interpretation::toString_Assigns() {
  std::string retval = "";
  std::vector<domain::Vector_Assign*> &id = domain_->getVectorAssigns();
  for (std::vector<domain::Vector_Assign *>::iterator it = id.begin(); it != id.end(); ++it) {
      coords::Vector_Assign* coords = coords2dom_->getVector_Assign(*it);
      interp::Vector_Assign *interp = coords2interp_->getVector_Assign(coords);
      retval = retval.append(interp->toString()).append("\n");
  }
  return retval;
}

std::string Interpretation::toString_FloatIdents() {
    std::string retval = "";
    std::vector<domain::FloatIdent*> &id = domain_->getFloatIdents();
    for (std::vector<domain::FloatIdent *>::iterator it = id.begin(); it != id.end(); ++it) {
        coords::FloatIdent* coords = coords2dom_->getFloatIdent(*it);
        interp::FloatIdent *interp = coords2interp_->getFloatIdent(coords);
        retval = retval.append(interp->toString());
        retval = retval.append("\n"); 
    }
    return retval;
}

std::string Interpretation::toString_FloatExprs() {
  std::string retval = "";
  std::vector<domain::FloatExpr*> &id = domain_->getFloatExprs();
  for (std::vector<domain::FloatExpr *>::iterator it = id.begin(); it != id.end(); ++it) {
      coords::FloatExpr* coords = coords2dom_->getFloatExpr(*it);
      interp::FloatExpr *interp = coords2interp_->getFloatExpr(coords);
      retval = retval.append(interp->toString());
      retval = retval.append("\n");
  }
  return retval;
}

std::string Interpretation::toString_Floats() {
  std::string retval = "";
  std::vector<domain::Float*> &id = domain_->getFloats();
  for (std::vector<domain::Float *>::iterator it = id.begin(); it != id.end(); ++it) {
      coords::Float* coords = coords2dom_->getFloat(*it);
      interp::Float *interp = coords2interp_->getFloat(coords);   
      retval = retval
      .append("(")
      .append(interp->toString())
      .append(" : vec ")
      .append((*it)->getSpaceContainer()->toString())
      .append(")\n");
  }
  return retval;
}

std::string Interpretation::toString_FloatDefs() {
  std::string retval = "";
  std::vector<domain::Float_Def*> &id = domain_->getFloatDefs();
  for (std::vector<domain::Float_Def *>::iterator it = id.begin(); it != id.end(); ++it) {
      coords::Float_Def* coords = coords2dom_->getFloat_Def(*it);
      interp::Float_Def *interp = coords2interp_->getFloat_Def(coords);
      retval = retval.append(interp->toString()).append("\n");
  }
  return retval;
}

std::string Interpretation::toString_FloatAssigns() {
  std::string retval = "";
  std::vector<domain::Float_Assign*> &id = domain_->getFloatAssigns();
  for (std::vector<domain::Float_Assign *>::iterator it = id.begin(); it != id.end(); ++it) {
      coords::Float_Assign* coords = coords2dom_->getFloat_Assign(*it);
      interp::Float_Assign *interp = coords2interp_->getFloat_Assign(coords);
      retval = retval.append(interp->toString()).append("\n");
  }
  return retval;
}





void Interpretation::setAll_Spaces() {
  auto vecIdents = domain_->getVecIdents();
  auto vecExprs = domain_->getVecExprs();
  auto vecs = domain_->getVectors();
  auto vecDefs = domain_->getVectorDefs();

  for(auto beg = vecIdents.begin(); beg != vecIdents.end(); beg++)
  {

    auto p = *beg;

    coords::VecIdent *coords = coords2dom_->getVecIdent(*beg);
    domain::Space& space = oracle_->getSpaceForVecIdent(coords);
    p->setSpace(&space);

  }

  for(auto beg = vecExprs.begin(); beg != vecExprs.end(); beg++)
  {
    auto ve = *beg;

    auto vve = (domain::VecVarExpr*)ve;
    auto vpr = (domain::VecParenExpr*)ve;
    auto vvae = (domain::VecVecAddExpr*)ve;

    coords::VecExpr *coords = coords2dom_->getVecExpr(*beg);

    auto cvve = (coords::VecVarExpr*)coords;
    auto cvvpr = (coords::VecParenExpr*)coords;
    auto cvvae = (coords::VecVecAddExpr*)coords;

    if(vve)
    {

      domain::Space& space = oracle_->getSpaceForVecVarExpr(coords);
      ve->setSpace(&space);
    }
    else if(vpr)
    {

      domain::Space& space = oracle_->getSpaceForVecParenExpr(coords);
      ve->setSpace(&space);
    }
    else if(vvae)
    {
      auto left = (coords::VecExpr*) cvvae->getLeft();
      auto right = (coords::VecExpr*) cvvae->getRight();

      domain::Space& space = oracle_->getSpaceForAddExpression(left, right);
      ve->setSpace(&space);
    }
    
  }

  for(auto beg = vecs.begin(); beg != vecs.end(); beg++)
  {
    auto vec = *beg;

    auto vl = (domain::Vector_Lit*)vec;
    auto ve = (domain::Vector_Expr*)vec;

    if(vl)
    {
      coords::Vector_Lit* cvl = coords2dom_->getVector_Lit(vl);

      domain::Space& s = oracle_->getSpaceForVector_Lit(cvl);
      vec->setSpace(&s);
    }
    else if(ve)
    {
      coords::Vector_Expr* cve = coords2dom_->getVector_Expr(ve);
      domain::Space& s = oracle_->getSpaceForVector_Expr(cve);
      vec->setSpace(&s);
    }

  }
  //not required for these
  for(auto beg = vecDefs.begin(); beg != vecDefs.end(); beg++)
  {
    auto vd = *beg;

    int i = 1;
  }

}

void Interpretation::mkVarTable(){
  auto vecIdents = domain_->getVecIdents();
  auto vecExprs = domain_->getVecExprs();
  auto vecs = domain_->getVectors();
  auto vecDefs = domain_->getVectorDefs();

  auto idx = 1;

  for(auto it = vecIdents.begin(); it != vecIdents.end();it++)
  {
    auto q = this->coords2dom_->getVecIdent(this->coords2dom_->getVecIdent(*it));

    this->index2coords_[idx++]=(coords::Coords*)this->coords2dom_->getVecIdent(*it);//static_cast<coords::Coords*>(this->coords2dom_->getVecIdent(*it));
    //this->index2dom_[idx++]=
  }
 // std::cout<<idx<<std::endl;
  for(auto it = vecExprs.begin(); it != vecExprs.end();it++)
  {
    auto q = this->coords2dom_->getVecExpr(this->coords2dom_->getVecExpr(*it));
    this->index2coords_[idx++]=(coords::Coords*)this->coords2dom_->getVecExpr(*it);//static_cast<coords::Coords*>(this->coords2dom_->getVecExpr(*it));
  }
 // std::cout<<idx<<std::endl;
  for(auto it = vecs.begin(); it != vecs.end(); it++)
  {

    auto q = this->coords2dom_->getVector(this->coords2dom_->getVector(*it));

    this->index2coords_[idx++]=(coords::Coords*)this->coords2dom_->getVector(*it);//static_cast<coords::Coords*>(this->coords2dom_->getVector(*it));

  }
  //std::cout<<idx<<std::endl;
  /*
  for(auto it = vecDefs.begin(); it != vecDefs.end(); it++)
  {
    this->index2coords_[idx++]=static_cast<coords::Coords*>(this->coords2dom_->getVector_Def(*it));

  }
  */
  auto floatIdents = domain_->getFloatIdents();
  auto floatExprs = domain_->getFloatExprs();
  auto floats = domain_->getFloats();
  auto floatDefs = domain_->getFloatDefs();

  for(auto it = floatIdents.begin(); it != floatIdents.end();it++)
  {
    auto q = this->coords2dom_->getFloatIdent(this->coords2dom_->getFloatIdent(*it));

    this->index2coords_[idx++]=(coords::Coords*)this->coords2dom_->getFloatIdent(*it);//static_cast<coords::Coords*>(this->coords2dom_->getVecIdent(*it));
    //this->index2dom_[idx++]=
  }
  for(auto it = floatExprs.begin(); it != floatExprs.end();it++)
  {
    auto q = this->coords2dom_->getFloatExpr(this->coords2dom_->getFloatExpr(*it));
    this->index2coords_[idx++]=(coords::Coords*)this->coords2dom_->getFloatExpr(*it);//static_cast<coords::Coords*>(this->coords2dom_->getVecExpr(*it));

  }
  for(auto it = floats.begin(); it != floats.end(); it++)
  {

    auto q = this->coords2dom_->getFloat(this->coords2dom_->getFloat(*it));

    this->index2coords_[idx++]=(coords::Coords*)this->coords2dom_->getFloat(*it);//static_cast<coords::Coords*>(this->coords2dom_->getVector(*it));

  }
}

void Interpretation::printVarTable(){
  int sz = this->index2coords_.size();

  for(int i = 1; i<=sz;i++)
  {
    auto variable = this->index2coords_.at(i);
    auto v = static_cast<coords::Vector*>(variable);
    auto dom_v = this->coords2dom_->getVector(v);
    auto dom_vi = this->coords2dom_->getVecIdent((coords::VecIdent*)variable);
    auto dom_ve = this->coords2dom_->getVecExpr((coords::VecExpr*)variable);
    auto f = static_cast<coords::Float*>(variable);
    auto dom_f = this->coords2dom_->getFloat(f);
    auto dom_fi = this->coords2dom_->getFloatIdent((coords::FloatIdent*)variable);
    auto dom_fe = this->coords2dom_->getFloatExpr((coords::FloatExpr*)variable);


    if ((coords::Vector_Def*)variable and false){
      auto dom_vd = this->coords2dom_->getVector_Def((coords::Vector_Def*)variable);
      //std::cout<<"Index:"<<i<<", Physical Variable:"<<this->index2coords_.at(i)->toString()<<", Physical Type:"<<dom_vd->getSpaceContainer()->toString()<<std::endl;
    }
    else if(dom_v){
      std::cout<<"Index:"<<i<<", Vector: "<<variable->toString()<<", Source Location: "<<variable->getSourceLoc()<<", Physical Type: "<<dom_v->getSpaceContainer()->toString()<<std::endl;

    }
    else if(dom_vi){
      std::cout<<"Index:"<<i<<", Vec Ident: "<<variable->toString()<<", Source Location: "<<variable->getSourceLoc()<<", Physical Type: "<<dom_vi->getSpaceContainer()->toString()<<std::endl;

    }
    else if(dom_ve){
      std::cout<<"Index:"<<i<<", Vec Expr: "<<variable->toString()<<", Source Location: "<<variable->getSourceLoc()<<", Physical Type: "<<dom_ve->getSpaceContainer()->toString()<<std::endl;

    }
    else if(dom_f){
      std::cout<<"Index:"<<i<<", Float: "<<variable->toString()<<", Source Location: "<<variable->getSourceLoc()<<", Physical Type: "<<dom_f->getSpaceContainer()->toString()<<std::endl;

    }
    else if(dom_fi){
      std::cout<<"Index:"<<i<<", Float Ident: "<<variable->toString()<<", Source Location: "<<variable->getSourceLoc()<<", Physical Type: "<<dom_fi->getSpaceContainer()->toString()<<std::endl;

    }
    else if(dom_fe){
      std::cout<<"Index:"<<i<<", Float Expr: "<<variable->toString()<<", Source Location: "<<variable->getSourceLoc()<<", Physical Type: "<<dom_fe->getSpaceContainer()->toString()<<std::endl;

    }
  }

  /*
  for(auto it = this->index2coords_.begin(); it != this->index2coords_.end(); it++)
  {
    std::cout<<"Index:"<<it->first<<",Physical Variable:"<<it->second->toString()<<std::endl;
  }
  */
}

void Interpretation::updateVarTable(){
  auto vecIdents = domain_->getVecIdents();
  auto vecExprs = domain_->getVecExprs();
  auto vecs = domain_->getVectors();
  auto vecDefs = domain_->getVectorDefs();

  auto sz = (int)this->index2coords_.size()+1;
  try{
    std::cout<<"Enter 0 to print the Variable Table again. Enter the index of a Variable to update its physical type. Enter "<<sz<<" to exit and check."<<std::endl;
    int choice;
    std::cin >> choice;

    while((choice == 0 || this->index2coords_.find(choice) != this->index2coords_.end()) && choice != sz)
    {
      auto b = choice == 0;

      if(choice == 0){
        this->printVarTable();
      }
      else{

        auto v = this->index2coords_.find(choice)->second;

        auto cvi = dynamic_cast<coords::VecIdent*>(v);
        auto cvve = dynamic_cast<coords::VecVarExpr*>(v);
        auto cvpr = dynamic_cast<coords::VecParenExpr*>(v);
        auto cvvae = dynamic_cast<coords::VecVecAddExpr*>(v);
        auto cvsme = dynamic_cast<coords::VecScalarMulExpr*>(v);
        auto cvl = dynamic_cast<coords::Vector_Lit*>(v);
        auto cve = dynamic_cast<coords::Vector_Expr*>(v);


        auto dom_v = this->coords2dom_->getVector((coords::Vector*)v);
        auto dom_vi = this->coords2dom_->getVecIdent((coords::VecIdent*)v);
        auto dom_ve = this->coords2dom_->getVecExpr((coords::VecExpr*)v);

        

        domain::Space* space = nullptr;

        if(cvi){
          space = &this->oracle_->getSpaceForVecIdent(cvi);
        }
        else if(cvve){
          space = &this->oracle_->getSpaceForVecVarExpr(cvve);
        }
        else if (cvpr){
          space = &this->oracle_->getSpaceForVecParenExpr(cvpr);
        }
        else if(cvvae){
          auto left = (coords::VecExpr*) cvvae->getLeft();
          auto right = (coords::VecExpr*) cvvae->getRight();

          space = &this->oracle_->getSpaceForAddExpression(left, right);
        }
        else if(cvsme){
          auto left = (coords::VecExpr*) cvsme->getLeft();
          auto right = (coords::FloatExpr*) cvsme->getRight();

          space = &this->oracle_->getSpaceForMulExpression(left, right);
        }
        else if(cvl){
          space = &this->oracle_->getSpaceForVector_Lit(cvl);
        }
        else if(cve){
          space = &this->oracle_->getSpaceForVector_Expr(cve);
        }
        else{

        }



        auto csi = dynamic_cast<coords::FloatIdent*>(v);
        auto csvve = dynamic_cast<coords::FloatVarExpr*>(v);
        auto cspe = dynamic_cast<coords::FloatParenExpr*>(v);
        auto cssae = dynamic_cast<coords::FloatFloatAddExpr*>(v);
        auto cssme = dynamic_cast<coords::FloatFloatMulExpr*>(v);
        auto csl = dynamic_cast<coords::Float_Lit*>(v);
        auto cse = dynamic_cast<coords::Float_Expr*>(v);

        auto dom_f = this->coords2dom_->getFloat((coords::Float*)v);
        auto dom_fi = this->coords2dom_->getFloatIdent((coords::FloatIdent*)v);
        auto dom_fe = this->coords2dom_->getFloatExpr((coords::FloatExpr*)v);

        if(csi){
          space = &this->oracle_->getSpaceForFloatIdent(csi);
        }
        else if(csvve){
          space = &this->oracle_->getSpaceForFloatVarExpr(csvve);

        }
        else if(cspe){
          space = &this->oracle_->getSpaceForFloatParenExpr(cspe);

        }
        else if(cssae){
          auto left = (coords::FloatExpr*)cssae->getLeft();
          auto right = (coords::FloatExpr*)cssae->getRight();

          space = &this->oracle_->getSpaceForFloatAddExpression(left, right);

        }
        else if(cssme){
          auto left = (coords::FloatExpr*)cssme->getLeft();
          auto right = (coords::FloatExpr*)cssme->getRight();

          space = &this->oracle_->getSpaceForFloatMulExpression(left, right);

        }
        else if(csl){
          space = &this->oracle_->getSpaceForFloat_Lit(csl);

        }
        else if(cse){
          space = &this->oracle_->getSpaceForFloat_Expr(cse);

        }
        else{

        }
        if(dom_v){
          dom_v->setSpace(space);
        }
        else if(dom_vi){
          dom_vi->setSpace(space);
        }
        else if(dom_ve){
          dom_ve->setSpace(space);
        }


        if(dom_f){
          dom_f->setSpace(space);
        }
        else if(dom_fi){
          dom_fi->setSpace(space);
        }
        else if(dom_fe){
          dom_fe->setSpace(space);
        }

        
      }
      std::cout<<"Enter 0 to print the Variable Table again. Enter the index of a Variable to update its physical type. Enter "<<sz<<" to exit and check."<<std::endl;
      std::cin >> choice;
      try{
      if(choice == 0 || this->index2coords_.find(choice) != this->index2coords_.end()){
        choice = choice;
      }
      }
      catch(std::exception ex){
        std::cout<<ex.what()<<std::endl;
      }

    }
  }
  catch(std::exception& ex){
    std::cout<<ex.what();
  }

}

void Interpretation::buildTypedDeclList()
{ 
  auto spaces = domain_->getSpaces();
  auto vec_idents = domain_->getVecIdents();
  auto float_idents = domain_->getFloatIdents();
  auto vec_exprs = domain_->getVecExprs();
  auto float_exprs = domain_->getFloatExprs();
  std::list<domain::VecExpr*> vec_vars;
  std::list<domain::FloatExpr*> float_vars;
  std::copy_if (vec_exprs.begin(), vec_exprs.end(), std::back_inserter(vec_vars), [=](domain::VecExpr* ve){return dynamic_cast<domain::VecVarExpr*>(ve) != nullptr;} );
  std::copy_if (float_exprs.begin(), float_exprs.end(), std::back_inserter(float_vars), [=](domain::FloatExpr* fe){return dynamic_cast<domain::FloatVarExpr*>(fe) != nullptr;});

  std::vector<ast::VecIdent*> vec_with_space;
  std::vector<ast::FloatIdent*> float_with_space;

  for(auto var = vec_vars.begin(); var != vec_vars.end(); var++)
  {
    auto ast_ident = static_cast<ast::VecIdent*>(static_cast<ast::VecVarExpr*>(ast2coords_->coords_stmt->at(coords2dom_->getVecExpr(*var)))->getDecl());

    bool 
      has_space = std::find_if(spaces.begin(), spaces.end(), [=](domain::Space* space){ return space->getName() == (*var)->getSpaceContainer()->toString(); }) != spaces.end(),
      already_labeled = std::find(vec_with_space.begin(), vec_with_space.end(), ast_ident) != vec_with_space.end();

    //std::cout<<"has"<<std::to_string(has_space)<<"alr"<<std::to_string(already_labeled)<<std::endl;
    //ast_ident->dump();

    if(has_space and !already_labeled)
      vec_with_space.push_back(ast_ident);

  }

  for(auto ident = vec_idents.begin(); ident != vec_idents.end(); ident++)
  {
    auto ast_ident = static_cast<ast::VecIdent*>(ast2coords_->coords_decl->at(coords2dom_->getVecIdent(*ident)));

    bool 
      has_space = std::find_if(spaces.begin(), spaces.end(), [=](domain::Space* space){ return space->getName() == (*ident)->getSpaceContainer()->toString(); }) != spaces.end(),
      already_labeled = std::find(vec_with_space.begin(), vec_with_space.end(), ast_ident) != vec_with_space.end();

    //std::cout<<"has"<<std::to_string(has_space)<<"alr"<<std::to_string(already_labeled)<<std::endl;
    //ast_ident->dump();

    if(!has_space and !already_labeled)
      this->unconstrained_vecs.push_back(ast_ident);
   // if 
  }

  for(auto var = float_vars.begin(); var != float_vars.end(); var++)
  {
    auto ast_ident = static_cast<ast::FloatIdent*>(static_cast<ast::FloatVarExpr*>(ast2coords_->coords_stmt->at(coords2dom_->getFloatExpr(*var)))->getDecl());

    bool 
      has_space = std::find_if(spaces.begin(), spaces.end(), [=](domain::Space* space){ return space->getName() == (*var)->getSpaceContainer()->toString(); }) != spaces.end(),
      already_labeled = std::find(float_with_space.begin(), float_with_space.end(), ast_ident) != float_with_space.end();

    //std::cout<<"has"<<std::to_string(has_space)<<"alr"<<std::to_string(already_labeled)<<std::endl;
    //ast_ident->dump();

    if(has_space and !already_labeled)
      float_with_space.push_back(ast_ident);

  }

  for(auto ident = float_idents.begin(); ident != float_idents.end(); ident++)
  {
    auto ast_ident = static_cast<ast::FloatIdent*>(ast2coords_->coords_decl->at(coords2dom_->getFloatIdent(*ident)));

    bool 
      has_space = std::find_if(spaces.begin(), spaces.end(), [=](domain::Space* space){ return space->getName() == (*ident)->getSpaceContainer()->toString(); }) != spaces.end(),
      already_labeled = std::find(float_with_space.begin(), float_with_space.end(), ast_ident) != float_with_space.end();

    //std::cout<<"has"<<std::to_string(has_space)<<"alr"<<std::to_string(already_labeled)<<std::endl;
    //ast_ident->dump();

    if(!has_space and !already_labeled)
      this->unconstrained_floats.push_back(ast_ident);
   // if 
  }

  for(auto it = this->unconstrained_vecs.begin(); it != this->unconstrained_vecs.end();it++)
  {
    //std::cout<<"has"<<std::to_string((int)*it)<<"alr"<<std::endl;
    //(*it)->dump();
    std::cout<<"has"<<(*it)->getNameAsString()<<"alr"<<std::endl;
    unconstrained_vec_names.push_back((*it)->getNameAsString());
  }

  for(auto it = this->unconstrained_floats.end(); it != this->unconstrained_floats.end(); it++)
  {
    //std::cout<<"has"<<std::to_string((int)*it)<<"alr"<<std::endl;
    //(*it)->dump();
    std::cout<<"has"<<(*it)->getLocation().printToString(this->context_->getSourceManager())<<"alr"<<std::endl;
    unconstrained_float_names.push_back((*it)->getNameAsString());
  }

}

bool Interpretation::needsConstraint(clang::VarDecl* var)
{
  auto locStr = var->getNameAsString();//var->getLocation().printToString(this->context_->getSourceManager());

  std::cout<<"has"<<locStr<<"alr"<<std::endl;
    
  bool 
    is_vec = 
      std::find_if(this->unconstrained_vec_names.begin(), this->unconstrained_vec_names.end(), [=](std::string vec){ return vec == locStr;}) != this->unconstrained_vec_names.end(),
    is_float =     
      std::find_if(this->unconstrained_float_names.begin(), this->unconstrained_float_names.end(), [=](std::string flt){ return flt == locStr;}) != this->unconstrained_float_names.end();



  if(is_vec)
    std::cout<<"IS VEC"<<std::endl;
  else if(is_float)
    std::cout<<"IS FLOAT"<<std::endl;
  else
  {
    std::cout<<"NEITHER"<<std::endl;
    var->dump();
  }
  

  return 
    is_vec 
    or 
    is_float;
}
/*
bool Interpretation::needsConstraint(ast::VecIdent* ident)
{
  return std::find(this->unconstrained_vecs.begin(), this->unconstrained_vecs.end(), ident) != this->unconstrained_vecs.end();
}

bool Interpretation::needsConstraint(ast::FloatIdent* ident)
{
  return std::find(this->unconstrained_floats.begin(), this->unconstrained_floats.end(), ident) != this->unconstrained_floats.end();
}*/