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
  LOG(DBUG) << "Interpretation::mkVecIdent. ast=" << std::hex << ast << ", " << coords->toString() << "\n";
  //domain::Space &space = oracle_->getSpaceForVecIdent(coords);
  domain::VecIdent *dom = domain_->mkVecIdent();
  coords2dom_->putVecIdent(coords, dom);
  interp::VecIdent *interp = new interp::VecIdent(coords, dom);
  coords2interp_->putVecIdent(coords, interp);
  interp2domain_->putVecIdent(interp, dom);
}

void Interpretation::mkScalarIdent(ast::ScalarIdent *ast)
{
  coords::ScalarIdent *coords = ast2coords_->mkScalarIdent(ast, context_);
  LOG(DBUG) << "Interpretation::mkVecIdent. ast=" << std::hex << ast << ", " << coords->toString() << "\n";
  //domain::Space &space = oracle_->getSpaceForVecIdent(coords);
  domain::ScalarIdent *dom = domain_->mkScalarIdent();
  coords2dom_->putScalarIdent(coords, dom);
  interp::ScalarIdent *interp = new interp::ScalarIdent(coords, dom);
  coords2interp_->putScalarIdent(coords, interp);
  interp2domain_->putScalarIdent(interp, dom);
}

/*****
* Expr
*****/


void Interpretation::mkVecVarExpr(ast::VecVarExpr *ast/*, clang::ASTContext *c*/) {
    coords::VecVarExpr *coords = ast2coords_->mkVecVarExpr(ast, context_);
    LOG(DBUG) << "Interpretation::mkVecVarExpr. ast=" << std::hex << ast << ", " << coords->toString() << "\n";
    //ast->dump();
    //domain::Space &space = oracle_->getSpaceForVecVarExpr(coords);
    domain::VecVarExpr *dom = domain_->mkVecVarExpr();
    coords2dom_->PutVecVarExpr(coords, dom);
    interp::VecVarExpr *interp = new interp::VecVarExpr(coords,dom);
    coords2interp_->putVecVarExpr(coords, interp);
    interp2domain_->putVecVarExpr(interp,dom);
}

void Interpretation::mkScalarVarExpr(ast::ScalarVarExpr *ast/*, clang::ASTContext *c*/) {
    coords::ScalarVarExpr *coords = ast2coords_->mkScalarVarExpr(ast, context_);
    LOG(DBUG) << "Interpretation::mkScalarVarExpr. ast=" << std::hex << ast << ", " << coords->toString() << "\n";
    //ast->dump();
    //domain::Space &space = oracle_->getSpaceForVecVarExpr(coords);
    domain::ScalarVarExpr *dom = domain_->mkScalarVarExpr();
    coords2dom_->PutScalarVarExpr(coords, dom);
    interp::ScalarVarExpr *interp = new interp::ScalarVarExpr(coords,dom);
    coords2interp_->putScalarVarExpr(coords, interp);
    interp2domain_->putScalarVarExpr(interp,dom);
}

void Interpretation::mkVecVecAddExpr(ast::VecVecAddExpr *add_ast, const ast::VecExpr *mem_expr, const ast::VecExpr *arg_expr) {
  coords::VecExpr *mem_coords = static_cast<coords::VecExpr*>
                                  (ast2coords_->getStmtCoords(mem_expr));
  coords::VecExpr *arg_coords = static_cast<coords::VecExpr*>
                                  (ast2coords_->getStmtCoords(arg_expr));
  LOG(DBUG) << "Interpretation::mkVecVecAddExpr. ast=" << std::hex << add_ast << "\n";
  if (mem_coords == NULL || arg_coords == NULL) {
    LOG(FATAL) <<"Interpretation::mkVecVecAddExpr: bad coordinates. Mem coords "
            << std::hex << mem_coords << " arg coords "
            << std::hex << arg_coords << "\n";
  }
  coords::VecVecAddExpr *coords = ast2coords_->mkVecVecAddExpr(add_ast, context_, mem_coords, arg_coords);
  //domain::Space &space = oracle_->getSpaceForAddExpression(mem_coords, arg_coords);
  domain::VecExpr *dom_mem_expr = coords2dom_->getVecExpr(mem_coords);
  domain::VecExpr *dom_arg_expr = coords2dom_->getVecExpr(arg_coords);
  if (dom_mem_expr == NULL || dom_arg_expr == NULL) {
    LOG(DBUG) <<"Interpretation::mkVecVecAddExpr: bad domain exprs. Mem "
              << std::hex << dom_mem_expr << " Arg "
              << std::hex << dom_arg_expr << "\n";
  }
  domain::VecVecAddExpr *dom = domain_->mkVecVecAddExpr(dom_mem_expr, dom_arg_expr);
  coords2dom_->PutVecVecAddExpr(coords, dom);
  LOG(DBUG) << "Interpretation::mkVecVecAddExpr: Mem_Coords: " << mem_coords->toString() << "\n";
  LOG(DBUG) << "Interpretation::mkVecVecAddExpr: Arg_Coords: " << arg_coords->toString() << "\n";

  interp::Interp *mem_interp = coords2interp_->getVecExpr(mem_coords);  // dyn type's toString not being called
  std::string mi_str = mem_interp->toString();
  LOG(DBUG) << "Interpretation::mkVecVecAddExpr: Mem_Interp: " << mi_str << "\n";
  interp::Interp *arg_interp = coords2interp_->getVecExpr(arg_coords);
  LOG(DBUG) << "Interpretation::mkVecVecAddExpr: Arg_Interp: " << arg_interp->toString() << "\n";
  interp::VecVecAddExpr *interp = new interp::VecVecAddExpr(coords, dom, mem_interp, arg_interp);
  coords2interp_->putVecVecAddExpr(coords, interp); 
  interp2domain_->putVecVecAddExpr(interp,dom);
}

void Interpretation::mkVecScalarMulExpr(ast::VecScalarMulExpr *mul_ast, const ast::VecExpr *vec_expr, const ast::ScalarExpr *flt_expr) {
  coords::ScalarExpr *flt_coords = static_cast<coords::ScalarExpr*>
                                  (ast2coords_->getStmtCoords(flt_expr));
  coords::VecExpr *vec_coords = static_cast<coords::VecExpr*>
                                  (ast2coords_->getStmtCoords(vec_expr));
 

  coords::VecScalarMulExpr *coords = ast2coords_->mkVecScalarMulExpr(mul_ast, context_, flt_coords, vec_coords);
  //domain::Space &space = oracle_->getSpaceForAddExpression(mem_coords, arg_coords);
  domain::ScalarExpr *dom_flt_expr = coords2dom_->getScalarExpr(flt_coords);
  domain::VecExpr *dom_vec_expr = coords2dom_->getVecExpr(vec_coords);

  domain::VecScalarMulExpr *dom = domain_->mkVecScalarMulExpr(dom_vec_expr, dom_flt_expr);
  coords2dom_->PutVecScalarMulExpr(coords, dom);

  interp::Interp *flt_interp = coords2interp_->getScalarExpr(flt_coords);  // dyn type's toString not being called
  std::string mi_str = flt_interp->toString();
  interp::Interp *vec_interp = coords2interp_->getVecExpr(vec_coords);
  interp::VecScalarMulExpr *interp = new interp::VecScalarMulExpr(coords, dom, vec_interp, flt_interp);
  coords2interp_->putVecScalarMulExpr(coords, interp); 
  interp2domain_->putVecScalarMulExpr(interp,dom);
}

void Interpretation::mkVecParenExpr(ast::VecParenExpr *ast, ast::VecExpr *expr) { 
    coords::VecParenExpr *coords = ast2coords_->mkVecParenExpr(ast, context_, expr);   
    coords::VecExpr *expr_coords = static_cast<coords::VecExpr *>(ast2coords_->getStmtCoords(expr));
    LOG(DBUG) << 
      "Interpretation::mkVecParenExpr. ast=" << 
      std::hex << ast << ", " << coords->toString() << 
      "expr = " << expr_coords->toString() << "\n";
    //domain::Space &space = oracle_->getSpaceForVecParenExpr(coords);
    domain::VecExpr *dom_expr = coords2dom_->getVecExpr(expr_coords);
    domain::VecParenExpr *dom = domain_->mkVecParenExpr(dom_expr);
    coords2dom_->PutVecParenExpr(coords, dom);
    interp::VecExpr *expr_interp = coords2interp_->getVecExpr(expr_coords);
    interp::VecParenExpr *interp = new interp::VecParenExpr(coords, dom, expr_interp);
    coords2interp_->putVecParenExpr(coords, interp);  
    interp2domain_->putVecParenExpr(interp,dom);
} 

void Interpretation::mkScalarParenExpr(ast::ScalarParenExpr *ast, ast::ScalarExpr *expr) { 
    coords::ScalarParenExpr *coords = ast2coords_->mkScalarParenExpr(ast, context_, expr);   
    coords::ScalarExpr *expr_coords = static_cast<coords::ScalarExpr *>(ast2coords_->getStmtCoords(expr));
    LOG(DBUG) << 
      "Interpretation::mkScalarParenExpr. ast=" << 
      std::hex << ast << ", " << coords->toString() << 
      "expr = " << expr_coords->toString() << "\n";
    //domain::Space &space = oracle_->getSpaceForVecParenExpr(coords);
    domain::ScalarExpr *dom_expr = coords2dom_->getScalarExpr(expr_coords);
    domain::ScalarParenExpr *dom = domain_->mkScalarParenExpr(dom_expr);
    coords2dom_->PutScalarParenExpr(coords, dom);
    interp::ScalarExpr *expr_interp = coords2interp_->getScalarExpr(expr_coords);
    interp::ScalarParenExpr *interp = new interp::ScalarParenExpr(coords, dom, expr_interp);
    coords2interp_->putScalarParenExpr(coords, interp);  
    interp2domain_->putScalarParenExpr(interp,dom);
} 


void Interpretation::mkScalarScalarAddExpr(ast::ScalarScalarAddExpr *ast, const ast::ScalarExpr* lhs, const ast::ScalarExpr *rhs){
  coords::ScalarExpr *lhs_coords = static_cast<coords::ScalarExpr*>
                                  (ast2coords_->getStmtCoords(lhs));
  coords::ScalarExpr *rhs_coords = static_cast<coords::ScalarExpr*>
                                  (ast2coords_->getStmtCoords(rhs));
  LOG(DBUG) << "Interpretation::mkScalarScalarAddExpr. ast=" << std::hex << ast << "\n";

  coords::ScalarScalarAddExpr *coords = ast2coords_->mkScalarScalarAddExpr(ast, context_, lhs_coords, rhs_coords);
  //domain::Space &space = oracle_->getSpaceForAddExpression(mem_coords, arg_coords);
  domain::ScalarExpr *dom_lhs_expr = coords2dom_->getScalarExpr(lhs_coords);
  domain::ScalarExpr *dom_rhs_expr = coords2dom_->getScalarExpr(rhs_coords);


  domain::ScalarScalarAddExpr *dom = domain_->mkScalarScalarAddExpr(dom_lhs_expr, dom_rhs_expr);
  coords2dom_->PutScalarScalarAddExpr(coords, dom);
  
  LOG(DBUG) << "Interpretation::mkScalarScalarAddExpr: LHS_Coords: " << lhs_coords->toString() << "\n";
  LOG(DBUG) << "Interpretation::mkScalarScalarAddExpr: RHS_Coords: " << rhs_coords->toString() << "\n";

  interp::Interp *lhs_interp = coords2interp_->getScalarExpr(lhs_coords);  // dyn type's toString not being called
  std::string mi_str = lhs_interp->toString();
  interp::Interp *rhs_interp = coords2interp_->getScalarExpr(rhs_coords);
  interp::ScalarScalarAddExpr *interp = new interp::ScalarScalarAddExpr(coords, dom, lhs_interp, rhs_interp);
  coords2interp_->putScalarScalarAddExpr(coords, interp); 
  interp2domain_->putScalarScalarAddExpr(interp,dom);
}

void Interpretation::mkScalarScalarMulExpr(ast::ScalarScalarMulExpr *ast, const ast::ScalarExpr* lhs, const ast::ScalarExpr *rhs){
  coords::ScalarExpr *lhs_coords = static_cast<coords::ScalarExpr*>
                                  (ast2coords_->getStmtCoords(lhs));
  coords::ScalarExpr *rhs_coords = static_cast<coords::ScalarExpr*>
                                  (ast2coords_->getStmtCoords(rhs));
  LOG(DBUG) << "Interpretation::mkScalarScalarMulExpr. ast=" << std::hex << ast << "\n";
  if (lhs_coords == NULL || rhs_coords == NULL) {
    LOG(FATAL) <<"Interpretation::mkScalarScalarMulExpr: bad coordinates. lhs coords "
            << std::hex << lhs_coords << " rhs coords "
            << std::hex << rhs_coords << "\n";
  }
  coords::ScalarScalarMulExpr *coords = ast2coords_->mkScalarScalarMulExpr(ast, context_, lhs_coords, rhs_coords);

  domain::ScalarExpr *dom_lhs_expr = coords2dom_->getScalarExpr(lhs_coords);
  domain::ScalarExpr *dom_rhs_expr = coords2dom_->getScalarExpr(rhs_coords);
  if (dom_lhs_expr == NULL || dom_rhs_expr == NULL) {
    LOG(DBUG) <<"Interpretation::mkScalarScalarMulExpr: bad domain exprs. lhs "
              << std::hex << dom_lhs_expr << " rhs "
              << std::hex << dom_rhs_expr << "\n";
  }
  domain::ScalarScalarMulExpr *dom = domain_->mkScalarScalarMulExpr(dom_lhs_expr, dom_rhs_expr);
  coords2dom_->PutScalarScalarMulExpr(coords, dom);
  LOG(DBUG) << "Interpretation::mkScalarScalarMulExpr: lhs_Coords: " << lhs_coords->toString() << "\n";
  LOG(DBUG) << "Interpretation::mkScalarScalarMulExpr: rhs_Coords: " << rhs_coords->toString() << "\n";

  interp::Interp *lhs_interp = coords2interp_->getScalarExpr(lhs_coords);  // dyn type's toString not being called
  std::string mi_str = lhs_interp->toString();
  LOG(DBUG) << "Interpretation::mkScalarScalarMulExpr: lhs_Interp: " << mi_str << "\n";
  interp::Interp *rhs_interp = coords2interp_->getScalarExpr(rhs_coords);
  LOG(DBUG) << "Interpretation::mkScalarScalarMulExpr: rhs_Interp: " << rhs_interp->toString() << "\n";
  interp::ScalarScalarMulExpr *interp = new interp::ScalarScalarMulExpr(coords, dom, lhs_interp, rhs_interp);
  coords2interp_->putScalarScalarMulExpr(coords, interp); 
  interp2domain_->putScalarScalarMulExpr(interp,dom);
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
    
    domain::Vector_Lit *dom = domain_->mkVector_Lit(x, y, z);
    coords2dom_->putVector_Lit(coords, dom); 
    interp::Vector_Lit *interp = new interp::Vector_Lit(coords, dom);
    coords2interp_->putVector_Lit(coords, interp);
    interp2domain_->putVector_Lit(interp,dom);
}

void Interpretation::mkScalar_Lit(ast::Scalar_Lit *ast, float scalar) {
    coords::Scalar_Lit *coords = ast2coords_->mkScalar_Lit(ast, context_, scalar);  
    
    domain::Scalar_Lit *dom = domain_->mkScalar_Lit(scalar);
    coords2dom_->putScalar_Lit(coords, dom); 
    interp::Scalar_Lit *interp = new interp::Scalar_Lit(coords, dom);
    coords2interp_->putScalar_Lit(coords, interp);
    interp2domain_->putScalar_Lit(interp,dom);
}

void Interpretation::mkVector_Expr(
      ast::Vector_Expr *ctor_ast, ast::VecExpr* expr_ast/*, clang::ASTContext *c*/) {
    coords::Vector_Expr *ctor_coords = ast2coords_->mkVector_Expr(ctor_ast, context_, expr_ast);
    coords::VecExpr *expr_coords = static_cast<coords::VecExpr *>(ast2coords_->getStmtCoords(expr_ast));
    
    domain::VecExpr *expr_dom = coords2dom_->getVecExpr(expr_coords);
    domain::Vector_Expr *dom_vec = domain_->mkVector_Expr(expr_dom); 
    coords2dom_->putVector_Expr(ctor_coords, dom_vec);
    interp::VecExpr *expr_interp = coords2interp_->getVecExpr(expr_coords);
    interp::Vector_Expr *interp = new interp::Vector_Expr(ctor_coords, dom_vec, expr_interp);
    coords2interp_->putVector_Expr(ctor_coords, interp);
    interp2domain_->putVector_Expr(interp, dom_vec);
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
    
    interp::Vector_Assign *interp = new interp::Vector_Assign(assign_coords, dom_vec_assign, var_interp, vec_interp);
    coords2interp_->putVector_Assign(assign_coords, interp);
    interp2domain_->putVector_Assign(interp, dom_vec_assign);
}

void Interpretation::mkScalar_Expr(
      ast::Scalar_Expr *ctor_ast, ast::ScalarExpr* expr_ast/*, clang::ASTContext *c*/) {
    coords::Scalar_Expr *ctor_coords = ast2coords_->mkScalar_Expr(ctor_ast, context_, expr_ast);
    coords::ScalarExpr *expr_coords = static_cast<coords::ScalarExpr *>(ast2coords_->getStmtCoords(expr_ast));
    
    domain::ScalarExpr *expr_dom = coords2dom_->getScalarExpr(expr_coords);
    domain::Scalar_Expr *dom_flt = domain_->mkScalar_Expr(expr_dom); 
    coords2dom_->putScalar_Expr(ctor_coords, dom_flt);
    interp::ScalarExpr *expr_interp = coords2interp_->getScalarExpr(expr_coords);
    interp::Scalar_Expr *interp = new interp::Scalar_Expr(ctor_coords, dom_flt, expr_interp);
    coords2interp_->putScalar_Expr(ctor_coords, interp);
    interp2domain_->putScalar_Expr(interp, dom_flt);
}

void Interpretation::mkScalar_Def(ast::Scalar_Def *def_ast,  
                                  ast::ScalarIdent *id_ast, 
                                  ast::ScalarExpr *expr_ast)
{
    def_ast->dump();
    id_ast->dump();
    expr_ast->dump();

    coords::ScalarIdent *id_coords = static_cast<coords::ScalarIdent *>
      (ast2coords_->getDeclCoords(id_ast));

    std::cout<<"is this nul?"<<std::endl;
    std::cout<<(ast2coords_->getStmtCoords(expr_ast))->toString()<<std::endl;
    std::cout<<"is null???"<<std::endl;
    coords::Scalar *flt_coords = (coords::Scalar*)
      (ast2coords_->getStmtCoords(expr_ast));
    coords::Scalar_Def *def_coords = ast2coords_->mkScalar_Def(def_ast, context_, id_coords, flt_coords);
    domain::ScalarIdent *flt_ident = coords2dom_->getScalarIdent(id_coords);
    /*
    Here there is some subtlety. We don't know if what was left in our
    interpretation by previous work was a Vector_Lit or a Vector_Expr.
    So we check first for a Vector_Expr
    */
    domain::Scalar *flt = coords2dom_->getScalar(flt_coords);
    domain::Scalar_Def* dom_flt_def = 
      domain_->mkScalar_Def(flt_ident, flt); 
    coords2dom_->putScalar_Def(def_coords, dom_flt_def);
    interp::ScalarIdent *id_interp = coords2interp_->getScalarIdent(id_coords);
    interp::Interp *flt_interp = coords2interp_->getScalar(flt_coords);
    if(not flt_interp){
      flt_interp = coords2interp_->getScalarExpr(flt_coords);
    }
    interp::Scalar_Def *interp = new interp::Scalar_Def(def_coords, dom_flt_def, id_interp, flt_interp);
    coords2interp_->putScalar_Def(def_coords, interp);
    interp2domain_->putScalar_Def(interp, dom_flt_def);
}



void Interpretation::mkScalar_Assign(ast::Scalar_Assign *assign_ast,  
                                  ast::ScalarVarExpr *id_ast, 
                                  ast::ScalarExpr *expr_ast)
{
    coords::ScalarVarExpr *id_coords = static_cast<coords::ScalarVarExpr *>
      (ast2coords_->getStmtCoords(id_ast));
    coords::Scalar *float_coords = static_cast<coords::Scalar *>
      (ast2coords_->getStmtCoords(expr_ast));
    coords::Scalar_Assign *assign_coords = ast2coords_->mkScalar_Assign(assign_ast, context_, id_coords, float_coords);
    domain::ScalarVarExpr *float_varexpr = coords2dom_->getScalarVarExpr(id_coords);
    /*
    Here there is some subtlety. We don't know if what was left in our
    interpretation by previous work was a Scalar_Lit or a Scalar_Expr.
    So we check first for a Scalar_Expr
    */
    domain::Scalar *Scalar = coords2dom_->getScalar(float_coords);
    domain::Scalar_Assign* dom_float_assign = 
      domain_->mkScalar_Assign(float_varexpr, Scalar); 
    coords2dom_->putScalar_Assign(assign_coords, dom_float_assign);
    interp::ScalarVarExpr *id_interp = coords2interp_->getScalarVarExpr(id_coords);
    interp::ScalarExpr *float_interp = coords2interp_->getScalarExpr(float_coords);
    interp::Scalar_Assign *interp = new interp::Scalar_Assign(assign_coords, dom_float_assign, id_interp, float_interp);
    coords2interp_->putScalar_Assign(assign_coords, interp);
    interp2domain_->putScalar_Assign(interp, dom_float_assign);
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
       LOG(DBUG) <<"Interpretation::getVecExpr. Error. Undefined for key!\n";
    }
    return dom;
}

domain::ScalarExpr* Interpretation::getScalarExpr(ast::ScalarExpr* ast) {
    // we use these objects as key for query purposes
    coords::ScalarExpr *coords = 
        static_cast<coords::ScalarExpr *>(ast2coords_->getStmtCoords(ast));
    domain::ScalarExpr* dom = coords2dom_->getScalarExpr(coords);
    if (!dom) {
      LOG(DBUG) <<"Interpretation::getVecExpr. Error. Undefined for key!\n";
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

std::string Interpretation::toString_ScalarIdents() {
    std::string retval = "";
    std::vector<domain::ScalarIdent*> &id = domain_->getScalarIdents();
    for (std::vector<domain::ScalarIdent *>::iterator it = id.begin(); it != id.end(); ++it) {
        coords::ScalarIdent* coords = coords2dom_->getScalarIdent(*it);
        interp::ScalarIdent *interp = coords2interp_->getScalarIdent(coords);
        retval = retval.append(interp->toString());
        retval = retval.append("\n"); 
    }
    return retval;
}

std::string Interpretation::toString_ScalarExprs() {
  std::string retval = "";
  std::vector<domain::ScalarExpr*> &id = domain_->getScalarExprs();
  for (std::vector<domain::ScalarExpr *>::iterator it = id.begin(); it != id.end(); ++it) {
      coords::ScalarExpr* coords = coords2dom_->getScalarExpr(*it);
      interp::ScalarExpr *interp = coords2interp_->getScalarExpr(coords);
      retval = retval.append(interp->toString());
      retval = retval.append("\n");
  }
  return retval;
}

std::string Interpretation::toString_Scalars() {
  std::string retval = "";
  std::vector<domain::Scalar*> &id = domain_->getScalars();
  for (std::vector<domain::Scalar *>::iterator it = id.begin(); it != id.end(); ++it) {
      coords::Scalar* coords = coords2dom_->getScalar(*it);
      interp::Scalar *interp = coords2interp_->getScalar(coords);   
      retval = retval
      .append("(")
      .append(interp->toString())
      .append(" : vec ")
      .append((*it)->getSpaceContainer()->toString())
      .append(")\n");
  }
  return retval;
}

std::string Interpretation::toString_ScalarDefs() {
  std::string retval = "";
  std::vector<domain::Scalar_Def*> &id = domain_->getScalarDefs();
  for (std::vector<domain::Scalar_Def *>::iterator it = id.begin(); it != id.end(); ++it) {
      coords::Scalar_Def* coords = coords2dom_->getScalar_Def(*it);
      interp::Scalar_Def *interp = coords2interp_->getScalar_Def(coords);
      retval = retval.append(interp->toString()).append("\n");
  }
  return retval;
}

std::string Interpretation::toString_ScalarAssigns() {
  std::string retval = "";
  std::vector<domain::Scalar_Assign*> &id = domain_->getScalarAssigns();
  for (std::vector<domain::Scalar_Assign *>::iterator it = id.begin(); it != id.end(); ++it) {
      coords::Scalar_Assign* coords = coords2dom_->getScalar_Assign(*it);
      interp::Scalar_Assign *interp = coords2interp_->getScalar_Assign(coords);
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
    auto cvpr = (coords::VecParenExpr*)coords;
    auto cvvae = (coords::VecVecAddExpr*)coords;

    if(vve)
    {

      domain::Space& space = oracle_->getSpaceForVecVarExpr(cvve);
      ve->setSpace(&space);
    }
    else if(vpr)
    {

      domain::Space& space = oracle_->getSpaceForVecParenExpr(cvpr);
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
  //don't label statements
  /*for(auto beg = vecDefs.begin(); beg != vecDefs.end(); beg++)
  {
    auto vd = *beg;
  }*/

}
//make a printable, indexed table of variables that can have their types assigned by a user or oracle
void Interpretation::mkVarTable(){
  auto vecIdents = domain_->getVecIdents();
  auto vecExprs = domain_->getVecExprs();
  auto vecs = domain_->getVectors();
  auto vecDefs = domain_->getVectorDefs();

  auto idx = 1;

  for(auto it = vecIdents.begin(); it != vecIdents.end();it++)
  {
   // auto q = this->coords2dom_->getVecIdent(this->coords2dom_->getVecIdent(*it));

    this->index2coords_[idx++]=(coords::Coords*)this->coords2dom_->getVecIdent(*it);
  }

  for(auto it = vecExprs.begin(); it != vecExprs.end();it++)
  {
   // auto q = this->coords2dom_->getVecExpr(this->coords2dom_->getVecExpr(*it));
    this->index2coords_[idx++]=(coords::Coords*)this->coords2dom_->getVecExpr(*it);
  }

  for(auto it = vecs.begin(); it != vecs.end(); it++)
  {

   // auto q = this->coords2dom_->getVector(this->coords2dom_->getVector(*it));

    this->index2coords_[idx++]=(coords::Coords*)this->coords2dom_->getVector(*it);//static_cast<coords::Coords*>(this->coords2dom_->getVector(*it));

  }

  auto floatIdents = domain_->getScalarIdents();
  auto floatExprs = domain_->getScalarExprs();
  auto floats = domain_->getScalars();
  auto floatDefs = domain_->getScalarDefs();

  for(auto it = floatIdents.begin(); it != floatIdents.end();it++)
  {
   // auto q = this->coords2dom_->getScalarIdent(this->coords2dom_->getScalarIdent(*it));

    this->index2coords_[idx++]=(coords::Coords*)this->coords2dom_->getScalarIdent(*it);
  }
  for(auto it = floatExprs.begin(); it != floatExprs.end();it++)
  {
  //  auto q = this->coords2dom_->getScalarExpr(this->coords2dom_->getScalarExpr(*it));
    this->index2coords_[idx++]=(coords::Coords*)this->coords2dom_->getScalarExpr(*it);

  }
  for(auto it = floats.begin(); it != floats.end(); it++)
  {

 //   auto q = this->coords2dom_->getScalar(this->coords2dom_->getScalar(*it));

    this->index2coords_[idx++]=(coords::Coords*)this->coords2dom_->getScalar(*it);

  }
}

//print the indexed variable table for the user
void Interpretation::printVarTable(){
  int sz = this->index2coords_.size();

  for(int i = 1; i<=sz;i++)
  {
    auto variable = this->index2coords_.at(i);
    auto v = static_cast<coords::Vector*>(variable);
    auto dom_v = this->coords2dom_->getVector(v);
    auto dom_vi = this->coords2dom_->getVecIdent((coords::VecIdent*)variable);
    auto dom_ve = this->coords2dom_->getVecExpr((coords::VecExpr*)variable);
    auto f = static_cast<coords::Scalar*>(variable);
    auto dom_f = this->coords2dom_->getScalar(f);
    auto dom_fi = this->coords2dom_->getScalarIdent((coords::ScalarIdent*)variable);
    auto dom_fe = this->coords2dom_->getScalarExpr((coords::ScalarExpr*)variable);


    if ((coords::Vector_Def*)variable and false){
     // auto dom_vd = this->coords2dom_->getVector_Def((coords::Vector_Def*)variable);
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
      std::cout<<"Index:"<<i<<", Scalar: "<<variable->toString()<<", Source Location: "<<variable->getSourceLoc()<<", Physical Type: "<<dom_f->getSpaceContainer()->toString()<<std::endl;

    }
    else if(dom_fi){
      std::cout<<"Index:"<<i<<", Scalar Ident: "<<variable->toString()<<", Source Location: "<<variable->getSourceLoc()<<", Physical Type: "<<dom_fi->getSpaceContainer()->toString()<<std::endl;

    }
    else if(dom_fe){
      std::cout<<"Index:"<<i<<", Scalar Expr: "<<variable->toString()<<", Source Location: "<<variable->getSourceLoc()<<", Physical Type: "<<dom_fe->getSpaceContainer()->toString()<<std::endl;

    }
  }
}

//while loop where user can select a variable by index and provide a physical type for that variable
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
          auto right = (coords::ScalarExpr*) cvsme->getRight();

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



        auto csi = dynamic_cast<coords::ScalarIdent*>(v);
        auto csvve = dynamic_cast<coords::ScalarVarExpr*>(v);
        auto cspe = dynamic_cast<coords::ScalarParenExpr*>(v);
        auto cssae = dynamic_cast<coords::ScalarScalarAddExpr*>(v);
        auto cssme = dynamic_cast<coords::ScalarScalarMulExpr*>(v);
        auto csl = dynamic_cast<coords::Scalar_Lit*>(v);
        auto cse = dynamic_cast<coords::Scalar_Expr*>(v);

        auto dom_f = this->coords2dom_->getScalar((coords::Scalar*)v);
        auto dom_fi = this->coords2dom_->getScalarIdent((coords::ScalarIdent*)v);
        auto dom_fe = this->coords2dom_->getScalarExpr((coords::ScalarExpr*)v);

        if(csi){
          space = &this->oracle_->getSpaceForScalarIdent(csi);
        }
        else if(csvve){
          space = &this->oracle_->getSpaceForScalarVarExpr(csvve);

        }
        else if(cspe){
          space = &this->oracle_->getSpaceForScalarParenExpr(cspe);

        }
        else if(cssae){
          auto left = (coords::ScalarExpr*)cssae->getLeft();
          auto right = (coords::ScalarExpr*)cssae->getRight();

          space = &this->oracle_->getSpaceForScalarAddExpression(left, right);

        }
        else if(cssme){
          auto left = (coords::ScalarExpr*)cssme->getLeft();
          auto right = (coords::ScalarExpr*)cssme->getRight();

          space = &this->oracle_->getSpaceForScalarMulExpression(left, right);

        }
        else if(csl){
          space = &this->oracle_->getSpaceForScalar_Lit(csl);

        }
        else if(cse){
          space = &this->oracle_->getSpaceForScalar_Expr(cse);

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

/*
* Builds a list of variables that have a type either assigned or inferred.
* Used for runtime constraint generation/logging 
*/

void Interpretation::buildTypedDeclList()
{ 
  auto spaces = domain_->getSpaces();
  auto vec_idents = domain_->getVecIdents();
  auto float_idents = domain_->getScalarIdents();
  auto vec_exprs = domain_->getVecExprs();
  auto float_exprs = domain_->getScalarExprs();
  std::list<domain::VecExpr*> vec_vars;
  std::list<domain::ScalarExpr*> float_vars;
  std::copy_if (vec_exprs.begin(), vec_exprs.end(), std::back_inserter(vec_vars), [=](domain::VecExpr* ve){return dynamic_cast<domain::VecVarExpr*>(ve) != nullptr;} );
  std::copy_if (float_exprs.begin(), float_exprs.end(), std::back_inserter(float_vars), [=](domain::ScalarExpr* fe){return dynamic_cast<domain::ScalarVarExpr*>(fe) != nullptr;});

  std::vector<ast::VecIdent*> vec_with_space;
  std::vector<ast::ScalarIdent*> float_with_space;

  for(auto var = vec_vars.begin(); var != vec_vars.end(); var++)
  {
    auto ast_ident = static_cast<ast::VecIdent*>(static_cast<ast::VecVarExpr*>(ast2coords_->coords_stmt->at(coords2dom_->getVecExpr(*var)))->getDecl());

    bool 
      has_space = std::find_if(spaces.begin(), spaces.end(), [=](domain::Space* space){ return space->getName() == (*var)->getSpaceContainer()->toString(); }) != spaces.end(),
      already_labeled = std::find(vec_with_space.begin(), vec_with_space.end(), ast_ident) != vec_with_space.end();

    if(has_space and !already_labeled)
      vec_with_space.push_back(ast_ident);

  }

  for(auto ident = vec_idents.begin(); ident != vec_idents.end(); ident++)
  {
    auto ast_ident = static_cast<ast::VecIdent*>(ast2coords_->coords_decl->at(coords2dom_->getVecIdent(*ident)));

    bool 
      has_space = std::find_if(spaces.begin(), spaces.end(), [=](domain::Space* space){ return space->getName() == (*ident)->getSpaceContainer()->toString(); }) != spaces.end(),
      already_labeled = std::find(vec_with_space.begin(), vec_with_space.end(), ast_ident) != vec_with_space.end();


    if(!has_space and !already_labeled)
      this->unconstrained_vecs.push_back(ast_ident);
  }


  for(auto var = float_vars.begin(); var != float_vars.end(); var++)
  {
    auto ast_ident = static_cast<ast::ScalarIdent*>(static_cast<ast::ScalarVarExpr*>(ast2coords_->coords_stmt->at(coords2dom_->getScalarExpr(*var)))->getDecl());

    bool 
      has_space = std::find_if(spaces.begin(), spaces.end(), [=](domain::Space* space){ return space->getName() == (*var)->getSpaceContainer()->toString(); }) != spaces.end(),
      already_labeled = std::find(float_with_space.begin(), float_with_space.end(), ast_ident) != float_with_space.end();


    if(has_space and !already_labeled)
      float_with_space.push_back(ast_ident);

  }

  for(auto ident = float_idents.begin(); ident != float_idents.end(); ident++)
  {
    auto ast_ident = static_cast<ast::ScalarIdent*>(ast2coords_->coords_decl->at(coords2dom_->getScalarIdent(*ident)));

    bool 
      has_space = std::find_if(spaces.begin(), spaces.end(), [=](domain::Space* space){ return space->getName() == (*ident)->getSpaceContainer()->toString(); }) != spaces.end(),
      already_labeled = std::find(float_with_space.begin(), float_with_space.end(), ast_ident) != float_with_space.end();

    if(!has_space and !already_labeled){
      this->unconstrained_floats.push_back(ast_ident);
    }
   // if 
  }

  for(auto it = this->unconstrained_vecs.begin(); it != this->unconstrained_vecs.end();it++)
  {
    unconstrained_vec_names.push_back((*it)->getNameAsString());
  }

  for(auto it = this->unconstrained_floats.begin(); it != this->unconstrained_floats.end(); it++)
  {
    unconstrained_float_names.push_back((*it)->getNameAsString());
  }

}


/*
used for generating dynamic constraints.
given a variable, determine whether or not it does not have a type available (if so, a constraint must be registered)
*/
bool Interpretation::needsConstraint(clang::VarDecl* var)
{
  auto locStr = var->getNameAsString();
    
  bool 
    is_vec = 
      std::find_if(this->unconstrained_vec_names.begin(), this->unconstrained_vec_names.end(), [=](std::string vec){ return vec == locStr;}) != this->unconstrained_vec_names.end(),
    is_float =     
      std::find_if(this->unconstrained_float_names.begin(), this->unconstrained_float_names.end(), [=](std::string flt){ return flt == locStr;}) != this->unconstrained_float_names.end();

  

  return 
    is_vec 
    or 
    is_float;
}