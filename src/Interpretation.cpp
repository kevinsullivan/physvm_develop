/*
Establish interpretations for various AST nodes:

- 1. get required information from oracle 
- 2. create coordinates for object (updates ast2coords)
- 3. add (creates) corresponding domain object (linking back to coords)
- 4. update coords2domain

- TODO: factor back links from domain object into separate table
*/


#include "Interpretation.h"

using namespace interp;

Interpretation::Interpretation() {
//    coords_ = new coords::Coords();
    domain_ = new domain::Domain();
    oracle_ = new oracle::Oracle(domain_);
    ast2coords_ = new ast2coords::ASTToCoords();
    coords2dom_ = new coords2domain::CoordsToDomain();
}


/******
* Ident
******/

void Interpretation::mkVecIdent(ast::VecIdent *ast)
{
    std::cerr << "Interpretation::mkVecIdent. BEG\n";

    domain::Space &space = oracle_->getSpaceForVecIdent(ast);
    coords::VecIdent *coords = ast2coords_->mkVecIdent(ast);
    domain::VecIdent *dom = domain_->mkVecIdent(space, coords);
    coords2dom_->putVecIdent(coords, dom);

    std::cerr << "Interpretation::mkVecIdent *mkVecIdent: AST at " << std::hex 
        << ast << "; Coords at " << std::hex << coords 
        << ";  coords.toString is " << coords->toString() 
        << "; dom at " << std::hex << dom << "\n";
    std::cerr << "END Interpretation::mkVecIdent *mkVecIdent\n";
}


/*****
* Expr
*****/


void Interpretation::mkVecVarExpr(ast::VecVarExpr *ast/*, clang::ASTContext *c*/) {
    coords::VecVarExpr *var_coords = ast2coords_->mkVecVarExpr(ast);
    domain::Space& space = oracle_->getSpaceForVecVarExpr(ast);
    domain::VecVarExpr *dom_var = domain_->mkVecVarExpr(space, var_coords);
    coords2dom_->PutVecVarExpr(var_coords, dom_var);
}

void Interpretation::mkVecVecAddExpr(ast::VecVecAddExpr *ast, coords::VecExpr *mem_coords, coords::VecExpr *arg_coords) {

  std::cerr << "Interpretation::mkVecVecAddExpr: START: adding\n";
  std::cerr << "Interpretation::mkVecVecAddExpr: Member is " 
    << mem_coords->toString() << " \n";
  std::cerr << "Argument is " << arg_coords->toString() << "\n";
  std::cerr << "AST is (dump)";
  ast->dump();

  // - get coords of children in domain
  // - make coords for ast, including child coords
  // - update ast2coords map with new coords
  //
  //coords::VecExpr *mem_coords = mem->getCoords();
  //coords::VecExpr *arg_coords = arg->getCoords();
  if (mem_coords == NULL || arg_coords == NULL) {
    std::cerr << "Interpretation::mkVecVecAddExpr: bad coordinates. Mem coords " 
        << std::hex << mem_coords << " arg coords " 
        << std::hex << arg_coords << "\n";
  }
  coords::VecVecAddExpr *expr_coords = ast2coords_->mkVecVecAddExpr(ast, mem_coords, arg_coords);
/*  coords::VecVecAddExpr *stmt_coords = 
    new coords::VecVecAddExpr(ast, mem_coords, arg_coords);
  // private now?
  ast2coords_->overrideStmt(ast, stmt_coords);*/
 domain::Space &space = oracle_->getSpaceForAddExpression(mem, arg);
  domain::VecVecAddExpr *dom_add_expr = 
    domain_->mkVecVecAddExpr(space, expr_coords, mem, arg);
  coords2dom_->PutVecVecAddExpr(expr_coords, dom_add_expr);

  std::cerr << "Interpretation::mkVecVecAddExpr: Coords at " 
    << std::hex << expr_coords << "\n";
  std::cerr << "Interpretation::mkVecVecAddExpr: Adding add expr to domain: " 
    << dom_add_expr->toString() << "\n";
  std::cerr << "FINISHED: adding member call expression to system\n";
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
    std::cerr << "Interpretation::mkVector_Lit. START";
    std::cerr << "Interpretation::mkVector_Lit. WARN: Scalar stubbed.\n";
  
    coords::Vector_Lit *vec_coords = ast2coords_->mkVector_Lit(ast, 0.0);
    // TODO: Should we get space from oracle here, or infer from expr? One or other.
    //domain::Space& space = oracle_->getSpaceForVector_Lit(ast); // infer?
    domain::Vector_Lit *dom_var = domain_->mkVector_Lit(vec_coords);
    coords2dom_->putVector_Lit(vec_coords, dom_var);
    std::cerr << "Interpretation::mkVector_Lit. DONE\n";
}

/*
void Interpretation::mkVector_Var(
      ast::Vector_Var *ast, domain::VecVarExpr* expr, clang::ASTContext *c) {
    std::cerr << "Interpretation::mkVector_Var. START";
    coords::VecVarExpr *expr_coords = expr->getCoords();
    coords::Vector_Var *var_coords = ast2coords_->mkVector_Var(ast, expr_coords);
    oracle::Space& space = oracle_->getSpaceForVector_Var(ast, expr); // infer?
    domain::Vector_Var* dom_vec = domain_->mkVector_Var(space, vec_coords, expr);
    coords2dom_->PutVecVar(var_coords, dom_var);
    std::cerr << "Interpretation::mkVector_Var. DONE\n";
}
*/

void Interpretation::mkVector_Expr(
      ast::Vector_Expr *ast, coords::VecExpr* expr_coords/*, clang::ASTContext *c*/) {
    std::cerr << "Interpretation::mkVector_Expr. START";
    //coords::VecExpr *expr_coords = expr->getCoords();
    coords::Vector_Expr *vec_coords = ast2coords_->mkVector_Expr(ast, expr_coords);
    //domain::Space& space = oracle_->getSpaceForVector_Expr(ast, expr); // infer?

    // VecExpr should already be in dom, so look it up rather than creating it anew.
    domain::VecExpr *dom_expr = coords2dom_->getVecExpr(expr_coords);
//    domain::Vector_Expr* dom_vec = domain_->mkVector_Expr(vec_coords, dom_expr);

    domain::Vector_Expr *dom_vec = new domain::Vector_Expr(vec_coords, dom_expr);
    coords2dom_->PutVector_Expr(vec_coords, dom_vec);
    std::cerr << "Interpretation::mkVector_Expr. DONE\n";
}

/****
* Def
*****/

/****
 * Note: Have made decision that main communicates with Interpretation in terms
 * of coords, not in terms of domain objects.
 * */

void Interpretation::mkVector_Def(ast::Vector_Def *ast, coords::VecIdent *id_coords, coords::VecExpr *expr_coords)
{
    std::cerr << "START: Interpretation::mkVector_Def.\n.";
    if (!expr_coords || !id_coords) { std::cerr << "Interpretation::mkVector_Def: null arg\n"; }

    // No need for Space at this point, ident and vec already annotated
    // TODO: Move into ast2coords_->makeCoordsForVector_Def
    //coords::VecIdent *id_coords = id->getCoords();
    //coords::VecExpr *expr_coords = expr->getCoords();

    // TODO: Replace
    coords::Vector_Def *def_coords = ast2coords_->mkVector_Def(ast, id_coords, expr_coords);

    domain::Vector_Def* dom_vec_def = 
      domain_->mkVector_Def(ast, id_coords, expr_coords);
    coords2dom_->putVector_Def(def_coords, dom_vec_def);

    /*
    domain::Vector_Def *vec_def = domain_->putVector_Def(bind_coords, id, exp);
    coords2dom_->putVector_Def(bind_coords, vec_def);
    */
    std::cerr << 
        "Interpretation::mkVector_Def:\n";
        /* identifier at " << std::hex << id 
            << " wrapped addr is " << std::hex << id_coords->get() << "\n";
    std::cerr << "Interpretation::mkVector_Def: wrapped dump is \n";
    id_coords->get()->dump();
    std::cerr << "Interpretation::mkVector_Def: name is " << id_coords->toString() << "\n";
    std::cerr << "DONE: Interpretation::mkVector_Def..\n";*/
}

/*
// TODO: Refactor following code, it's out of place
const coords::VecExpr *Interpretation::getCoords(ast::VecExpr *expr)  // fix ret type name
{
    return ast2coords_->getCoords(expr);
}
*/
