#include "Interpretation.h"

using namespace interp;

Interpretation::Interpretation() {
//    coords_ = new coords::Coords();
    domain_ = new domain::Domain();
    oracle_ = new oracle::Oracle(domain_);
    ast2coords_ = new ast2coords::ASTToCoords();
    coords2dom_ = new coords2domain::CoordsToDomain();
}

/*
Establish interpretation for Vec identifier in AST
- get vector space
- create coordinates
- lift Vec to domain
*/
domain::VecIdent *Interpretation::mkVecIdent(ast::VecIdent *ast)
{
    cerr << "BEG interp::VecIdent *addVecIdent\n";
    domain::Space &space = oracle_->getSpaceForVecIdent(ast);
    const coords::VecIdent *coords = ast2coords_->makeCoordsForVecIdent(ast);
    domain::VecIdent *dom = domain_->addVecIdent(space, coords);
    coords2dom_->putVecIdentInterp(coords, dom);

    cerr << "domain::VecIdent *mkVecIdent: AST at " << std::hex << ast << "; Coords at " << std::hex << coords << ";  coords.toString is " << coords->toString() << "; dom at " << std::hex << dom << "\n";
    cerr << "END interp::VecIdent *addVecIdent\n";

    return dom;
}

void Interpretation::mkVecDef(ast::VecDef *ast, domain::VecIdent *id, domain::VecExpr *exp)
{
    cerr << "START: Interpretation::mkVecDef.\n.";
    if (!exp || !id)
    {
        cerr << "Interpretation::mkVecDef: null argument\n";
    }
    const coords::VecIdent *id_coords = id->getVarDeclWrapper();
    const coords::VecExpr *exp_coords = exp->getExpr();
    coords::VecDef *bind_coords = new coords::VecDef(ast, id_coords, exp_coords);
    ast2coords_->overrideStmt(ast, bind_coords);
    domain::VecDef &binding =
        domain_->addVecDef(bind_coords, id, exp);
    coords2dom_->putVecDefInterp(bind_coords, binding);
    cerr << 
        "Interpretation::mkVecDef: identifier at " << 
        std::hex << id << 
        " wrapped addr is " << std::hex << id_coords->get() <<
        "\n";
    cerr << "Interpretation::mkVecDef: wrapped dump is \n";
    id_coords->get()->dump();
    cerr << "Interpretation::mkVecDef: name is " << id_coords->toString() << "\n";
    cerr << "DONE: Interpretation::mkVecDef..\n";
}

// FIX
void Interpretation::mkVecVecAddExpr(ast::AddExpr *ast, domain::VecExpr *mem, domain::VecExpr *arg) {

  cerr << "Interpretation::mkVecVecAddExpr: START: adding\n";
  cerr << "Interpretation::mkVecVecAddExpr: Member is " << mem->toString() << " \n";
  cerr << "Argument is " << arg->toString() << "\n";
  cerr << "AST is (dump)";
  ast->dump();

  // Coords: 
  // - get coords of children in domain
  // - make coords for ast, including child coords
  // - update ast2coords map with new coords
  //
  // TODO: Abstract
  //
  const coords::VecExpr *mem_coords = mem->getCoords();
  const coords::VecExpr *arg_coords = arg->getCoords();
  if (mem_coords == NULL || arg_coords == NULL) {
    cerr << "Interpretation::mkVecVecAddExpr: bad coordinates. Mem coords " 
        << std::hex << mem_coords << " arg coords " 
        << std::hex << arg_coords << "\n";
  }

  coords::VecVecAddExpr *expr_coords = 
    new coords::VecVecAddExpr(ast, mem_coords, arg_coords);
  ast2coords_->overrideExpr(ast, expr_coords);
  domain::Space &space = oracle_->getSpaceForAddExpression(mem, arg);
  domain::VecExpr *dom_add_expr = domain_->addVecVecAddExpr(space, expr_coords, mem, arg);
  coords2dom_->putExpressionInterp(expr_coords, dom_add_expr);

  cerr << "Interpretation::mkVecVecAddExpr: Coords at " 
    << std::hex << expr_coords << "\n";
  cerr << "Interpretation::mkVecVecAddExpr: Adding add expr to domain: " 
    << dom_add_expr->toString() << "\n";
  cerr << "FINISHED: adding member call expression to system\n";
}

// TODO: Factor this stuff out of preceding procedures
void Interpretation::mkVecExpr(ast::VecExpr *ast, ASTContext *context) {
    cerr << "Interpretation::mkVecExpr. START";
    coords::Vector *vcoords = new coords::Vector(ast);  
    ast2coords_->overrideExpr(ast, vcoords);
    // WARNING: Is following code right? Or meant for CTORs?
    domain::VecExpr *vec = domain_->addVector(vcoords);
    coords2dom_->putExpressionInterp(vcoords, vec);
    cerr << "Interpretation::mkVecExpr. DONE.\n";
}


/* Future work
void Interpretation::mkVecVarExpr(ast, mem_coords, arg_coords) {
    const coords::VecVarExpr *var_coords = new VarDeclRef(ast);
    ast2coords_->overrideExpr(ast, var_coords));
    domain::VecExpr &be = domain_domain->addVecVarExpr(var_coords);
    coords2dom_->putExpressionInterp(*wrapper, be);
}
*/

void Interpretation::mkVector(ast::VecLitExpreral *ast, ASTContext *context) {
    cerr << "Interpretation::mkVector(VecLitExpr). START";
    coords::Vector *vec_coords = new coords::Vector(ast);  // ???ctor!
    ast2coords_->overrideExpr(ast, vec_coords);
    domain::Vector* vec = domain_->addVector(vec_coords);
    coords2dom_->putVectorInterp(vec_coords, vec);
    cerr << "DONE Interpretation::mkVector(VecLitExpr)\n";
}

void Interpretation::mkVector(CXXConstructExpr *ctor_ast, ASTContext *context) {
    cerr << "Interpretation::mkVector(Expr). START\n";
    coords::Vector *vcoords = new coords::Vector(ast);  // ???ctor!
    ast2coords_->overrideExpr(ast, vcoords);
    domain::Vector* vec = domain_->addVector(vcoords);
    coords2dom_->putVectorInterp(vcoords, vec);
    cerr << "DONE Interpretation::mkVector(Expr)\n";
}

const coords::VecExpr *Interpretation::getCoords(ast::VecExpr *expr)  // fix ret type name
{
    return ast2coords_->getASTExprCoords(expr);
}