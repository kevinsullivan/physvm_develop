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

void Interpretation::mkVecIdent(ast::VecIdent *ast)
{
    std::cerr << "BEG interp::VecIdent *mkVecIdent\n";

    domain::Space &space = oracle_->getSpaceForVecIdent(ast);
    const coords::VecIdent *coords = new coords::VecIdent(ast);
    ast2coords_->overrideStmt(ast, coords);
    domain::VecIdent *dom = domain_->mkVecIdent(space, coords);
    coords2dom_->putVecIdent(coords, dom);

    std::cerr << "domain::VecIdent *mkVecIdent: AST at " << std::hex 
        << ast << "; Coords at " << std::hex << coords 
        << ";  coords.toString is " << coords->toString() 
        << "; dom at " << std::hex << dom << "\n";
    std::cerr << "END interp::VecIdent *mkVecIdent\n";
}


/*
When generating interpretation, we know subtypes of vector expressions
(literal, variable, function application), and so do not need and should
not use a generic putter. The benefit of not doing so is type checking 
and conceptual integrity. On the other hand, the putters for different
kinds of expressions do put them all in the same "expressions" table, 
as we do want to construct expressions inductively based on sum types. 
*/

/*
TODO: A procedure to "make coordinate for given AST node". Observation: we use
the same kinds of coordinates for *all* kinds of AST nodes. This is actually 
important. We want a homogenous system of code coordinates.
*/

// TODO: Change ast::VecLitExpr to ast::Vector_Lit
void Interpretation::mkVector_Lit(ast::VecLitExpr *ast, clang::ASTContext *c) {
    coords::VecLitExpr *var_coords = new coords::VecLitExpr(ast);
    ast2coords_->overrideStmt(ast, var_coords);
    oracle::Space& space = oracle_->getSpaceForVecLitExpr(ast);
    domain::VecLitExpr *dom_var = domain_->mkVecLitExpr(space, dom_var);
    coords2dom_->PutVecExpr(var_coords, dom_var);
}

void Interpretation::mkVecVarExpr(ast::VecVarExpr *ast, clang::ASTContext *c) {
    coords::VecVarExpr *var_coords = new coords::VecVarExpr(ast);
    ast2coords_->overrideStmt(ast, var_coords);
    domain::Space& space = oracle_->getSpaceForVecVarExpr(ast);
    domain::VecVarExpr *dom_var = domain_->mkVecVarExpr(space, dom_var);
    coords2dom_->PutVecExpr(var_coords, dom_var);
}

// TODO: FIX?
void Interpretation::mkVecVecAddExpr(ast::VecVecAddExpr *ast, domain::VecExpr *mem, domain::VecExpr *arg) {

  std::cerr << "Interpretation::mkVecVecAddExpr: START: adding\n";
  std::cerr << "Interpretation::mkVecVecAddExpr: Member is " << mem->toString() << " \n";
  std::cerr << "Argument is " << arg->toString() << "\n";
  std::cerr << "AST is (dump)";
  ast->dump();

  // - get coords of children in domain
  // - make coords for ast, including child coords
  // - update ast2coords map with new coords
  //
  const coords::VecExpr *mem_coords = mem->getCoords();
  const coords::VecExpr *arg_coords = arg->getCoords();
  if (mem_coords == NULL || arg_coords == NULL) {
    std::cerr << "Interpretation::mkVecVecAddExpr: bad coordinates. Mem coords " 
        << std::hex << mem_coords << " arg coords " 
        << std::hex << arg_coords << "\n";
  }

  coords::VecVecAddExpr *stmt_coords = 
    new coords::VecVecAddExpr(ast, mem_coords, arg_coords);
  ast2coords_->overrideStmt(ast, stmt_coords);
  domain::Space &space = oracle_->getSpaceForAddExpression(mem, arg);
  domain::VecExpr *dom_add_expr = domain_->mkVecVecAddExpr(space, stmt_coords, mem, arg);
  coords2dom_->PutVecExpr(stmt_coords, dom_add_expr);

  std::cerr << "Interpretation::mkVecVecAddExpr: Coords at " 
    << std::hex << stmt_coords << "\n";
  std::cerr << "Interpretation::mkVecVecAddExpr: Adding add expr to domain: " 
    << dom_add_expr->toString() << "\n";
  std::cerr << "FINISHED: adding member call expression to system\n";
}


/*
Vectors are fully "constructed" objects. We're seeing a bit of Clang AST
design showing through here, as clang separated things like function appl
expressions and objects constructed from them.

TODO: Rethink. Do we need separate mkVector for different AST-level vector 
constructor forms (lit, expr, and presumably var, in the future)? Or on the
other hand, should we suppress this distinction at this point? Presumably
"Clang is wise", but we'll have to think about that. A "design question."
*/
void Interpretation::mkVector_Lit(ast::Vector *ast, clang::ASTContext *context) {
    std::cerr << "Interpretation::mkVector. START";

// TODO: Fix - no Lit expr, it's ctor
    coords::VecExpr *vec_coords = new coords::VecLitExpr(ast);  
    ast2coords_->overrideStmt(ast, vec_coords);       
    domain::Space &s = oracle_->getSpaceForVector(ast);
    ast2coords_->overrideStmt(ast, vec_coords);
    domain::Vector* dom_vec = domain_->mkVector_Lit(space, vec_coords);
    coords2dom_->putVector_Lit(vec_coords, dom_vec);
    std::cerr << "DONE Interpretation::mkVector\n";
}


void Interpretation::mkVector_Expr(ast::Vector *vec, domain::VecExpr* expr, clang::ASTContext *context) {
    std::cerr << "Interpretation::mkVector. START";

    coords::Vector *vec_coords = new coords::VecVecAddExpr(vec);    // Fix - not an expr
    ast2coords_->overrideStmt(vec, vec_coords); 
    oracle::Space &s = oracle_->getSpaceForVector(vec);
    ast2coords_->overrideStmt(vec, vec_coords);
    domain::Vector* dom_vec = domain_->mkVector_Expr(space, vec_coords, expr);
    coords2dom_->putVectorInterp(vec_coords, dom_vec);
    std::cerr << "DONE Interpretation::mkVector\n";
}


void Interpretation::mkVecDef(ast::VecDef *ast, domain::VecIdent *id, domain::VecExpr *vec)
{
    std::cerr << "START: Interpretation::mkVecDef.\n.";
    if (!exp || !id) { std::cerr << "Interpretation::mkVecDef: null arg\n"; }

    // No need for Space at this point, ident and vec already annotated
    // TODO: Move into ast2coords_->makeCoordsForVecDef
    const coords::VecIdent *id_coords = id->getVarDeclWrapper();
    const coords::VecExpr *vec_coords = vec->getVecExpr();
    coords::VecDef *bind_coords = new coords::VecDef(ast, id_coords, vec_coords);
    ast2coords_->overrideStmt(ast, bind_coords);

    domain::VecDef *vec_def = domain_->putVecDef(bind_coords, id, exp);
    coords2dom_->putVecDef(bind_coords, vec_def);

    std::cerr << 
        "Interpretation::mkVecDef: identifier at " << std::hex << id 
            << " wrapped addr is " << std::hex << id_coords->get() << "\n";
    std::cerr << "Interpretation::mkVecDef: wrapped dump is \n";
    id_coords->get()->dump();
    std::cerr << "Interpretation::mkVecDef: name is " << id_coords->toString() << "\n";
    std::cerr << "DONE: Interpretation::mkVecDef..\n";
}



const coords::VecExpr *Interpretation::getCoords(ast::VecExpr *expr)  // fix ret type name
{
    return ast2coords_->getCoords(expr);
}
