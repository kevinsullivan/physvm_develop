/*
Establish interpretations for various AST nodes:

- 1. get required information from oracle 
- 2. create coordinates for object, updating ast-coord bijection
- 3. add corresponding domain object, updating coord-domain bijection
*/

// TODO: These two can be integrated
#include "Interpretation.h"
#include "Interp.h"
#include "CoordsToInterp.h"
#include "InterpToDomain.h"

#include <g3log/g3log.hpp>



using namespace interp;

Interpretation::Interpretation() {
    domain_ = new domain::Domain();
    oracle_ = new oracle::Oracle(domain_);
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
    //LOG(DEBUG) <<"Interpretation::mkVecIdent. BEG\n";
    domain::Space &space = oracle_->getSpaceForVecIdent(ast);
    coords::VecIdent *coords = ast2coords_->mkVecIdent(ast);
    domain::VecIdent *dom = domain_->mkVecIdent(space); 
    coords2dom_->putVecIdent(coords, dom);

    interp::VecIdent *interp = new interp::VecIdent(coords,dom);
    coords2interp_->putVecIdent(coords, interp);
    interp2domain_->putVecIdent(interp,dom);
}


/*****
* Expr
*****/


void Interpretation::mkVecVarExpr(ast::VecVarExpr *ast/*, clang::ASTContext *c*/) {
    coords::VecVarExpr *coords = ast2coords_->mkVecVarExpr(ast);
    domain::Space& space = oracle_->getSpaceForVecVarExpr(ast);
    domain::VecVarExpr *dom = domain_->mkVecVarExpr(space);
    coords2dom_->PutVecVarExpr(coords, dom);

    interp::VecVarExpr *interp = new interp::VecVarExpr(coords,dom);
    coords2interp_->putVecVarExpr(coords, interp);
    interp2domain_->putVecVarExpr(interp,dom);
}


void Interpretation::mkVecVecAddExpr(ast::VecVecAddExpr *add_ast, const ast::VecExpr *mem_expr, const ast::VecExpr *arg_expr) {
  coords::VecExpr *mem_coords = static_cast<coords::VecExpr*>
                                  (ast2coords_->getStmtCoords(mem_expr));
  coords::VecExpr *arg_coords = static_cast<coords::VecExpr*>
                                  (ast2coords_->getStmtCoords(arg_expr));
  if (mem_coords == NULL || arg_coords == NULL) {
    LOG(FATAL) <<"Interpretation::mkVecVecAddExpr: bad coordinates. Mem coords "
            << std::hex << mem_coords << " arg coords "
            << std::hex << arg_coords << "\n";
  }
  coords::VecVecAddExpr *coords = ast2coords_->mkVecVecAddExpr(add_ast, mem_coords, arg_coords);
  domain::Space &space = oracle_->getSpaceForAddExpression(mem_coords, arg_coords);
  domain::VecExpr *dom_mem_expr = coords2dom_->getVecExpr(mem_coords);
  domain::VecExpr *dom_arg_expr = coords2dom_->getVecExpr(arg_coords);
  if (dom_mem_expr == NULL || dom_arg_expr == NULL) {
    LOG(DEBUG) <<"Interpretation::mkVecVecAddExpr: bad domain exprs. Mem "
              << std::hex << dom_mem_expr << " Arg "
              << std::hex << dom_arg_expr << "\n";
  }
  domain::VecVecAddExpr *dom = domain_->mkVecVecAddExpr(space, dom_mem_expr, dom_arg_expr);
  coords2dom_->PutVecVecAddExpr(coords, dom);

  interp::Interp *mem_interp = coords2interp_->getVecExpr(mem_coords);
  interp::Interp *arg_interp = coords2interp_->getVecExpr(arg_coords);
  interp::VecVecAddExpr *interp = new interp::VecVecAddExpr(coords, dom, mem_interp, arg_interp);
  coords2interp_->putVecVecAddExpr(coords, interp); 
  interp2domain_->putVecVecAddExpr(interp,dom);
}


/*******
* Vector
*******/

/*
Vectors are fully "constructed" objects. We're seeing a bit of Clang AST
design showing through here, as clang separated things like function appl
expressions and objects constructed from them.
*/

void Interpretation::mkVector_Lit(ast::Vector_Lit *ast/*, clang::ASTContext *c*/) {
  //  LOG(DEBUG) <<"Interpretation::mkVector_Lit. START";
  //  LOG(DEBUG) <<"Interpretation::mkVector_Lit. WARN: Scalar stubbed.\n";
  
    coords::Vector_Lit *coords = ast2coords_->mkVector_Lit(ast, 0.0);
    domain::Space& s = oracle_->getSpaceForVector_Lit(ast);  //*new domain::Space("Interpretation::mkVector_Expr:: Warning. Using Stub Space\n.");
    domain::Vector_Lit *dom = domain_->mkVector_Lit(s);
    coords2dom_->putVector_Lit(coords, dom); 

    interp::Vector_Lit *interp = new interp::Vector_Lit(coords, dom);
    coords2interp_->putVector_Lit(coords, interp);
    interp2domain_->putVector_Lit(interp,dom);


  //  LOG(DEBUG) <<"Interpretation::mkVector_Lit. DONE\n";
}

void Interpretation::mkVector_Expr(
      ast::Vector_Expr *ctor_ast, ast::VecExpr* expr_ast/*, clang::ASTContext *c*/) {

  //  LOG(DEBUG) <<"Interpretation::mkVector_Expr. START. Warn: possibly wrong. Same ast for expr and ctor.";
    coords::Vector_Expr *ctor_coords = ast2coords_->mkVector_Expr(ctor_ast, expr_ast);
    coords::VecExpr *expr_coords = static_cast<coords::VecExpr *>(ast2coords_->getStmtCoords(expr_ast));
    domain::Space& s = oracle_->getSpaceForVector_Expr(ctor_ast);  //*new domain::Space("Interpretation::mkVector_Expr:: Warning. Using Stub Space\n.");
    domain::VecExpr *expr_dom = coords2dom_->getVecExpr(expr_coords);
    domain::Vector_Expr *dom_vec = domain_->mkVector_Expr(s, expr_dom); 
    coords2dom_->putVector_Expr(ctor_coords, dom_vec);

    interp::VecExpr *expr_interp = coords2interp_->getVecExpr(expr_coords);
    interp::Vector_Expr *interp = new interp::Vector_Expr(ctor_coords, dom_vec, expr_interp);
    coords2interp_->putVector_Expr(ctor_coords, interp);
    interp2domain_->putVector_Expr(interp, dom_vec);

    LOG(DEBUG) <<"Interpretation::mkVector_Expr. DONE\n";
}

/****
* Def
*****/

/****
 * Note: Have made decision that main communicates with Interpretation in terms
 * of coords, not in terms of domain objects.
 * */

void Interpretation::mkVector_Def(ast::Vector_Def *def_ast,  
                                  ast::VecIdent *id_ast, 
                                  ast::VecExpr *expr_ast)
{
    //LOG(DEBUG) <<"START: Interpretation::mkVector_Def.\n.";

    // TODO: Move into ast2coords_->makeCoordsForVector_Def
    coords::VecIdent *id_coords = static_cast<coords::VecIdent *>
      (ast2coords_->getDeclCoords(id_ast));
    coords::VecExpr *expr_coords = static_cast<coords::VecExpr *>
      (ast2coords_->getStmtCoords(expr_ast));
    coords::Vector_Def *def_coords = ast2coords_->mkVector_Def(def_ast, id_coords, expr_coords);

    domain::VecIdent *vec_ident = coords2dom_->getVecIdent(id_coords);
    domain::VecExpr *vec_expr = coords2dom_->getVecExpr(expr_coords);

    domain::Vector_Def* dom_vec_def = 
      domain_->mkVector_Def(vec_ident, vec_expr);
    coords2dom_->putVector_Def(def_coords, dom_vec_def);

    /*
    domain::Vector_Def *vec_def = domain_->putVector_Def(bind_coords, id, exp);
    coords2dom_->putVector_Def(bind_coords, vec_def);
  
    LOG(DEBUG) <<
        "Interpretation::mkVector_Def:\n";  */
        /* identifier at " << std::hex << id 
            << " wrapped addr is " << std::hex << id_coords->get() << "\n";
    LOG(DEBUG) <<"Interpretation::mkVector_Def: wrapped dump is \n";
    id_coords->get()->dump();
    LOG(DEBUG) <<"Interpretation::mkVector_Def: name is " << id_coords->toString() << "\n";
    LOG(DEBUG) <<"DONE: Interpretation::mkVector_Def..\n";*/
}

/*
coords::VecExpr *Interpretation::getCoords(ast::VecExpr *expr)  // fix ret type name
{
    return ast2coords_->getCoords(expr);
}
*/

