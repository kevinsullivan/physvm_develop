#include "Interpretation.h"

using namespace interp;

domain::Identifier *Interpretation::mkVecIdent(ast::Ident *ast)
{
    cerr << "BEG interp::VecIdent *addVecIdent\n";
    domain::Space &space = oracle_->getSpaceForIdentifier(ast);
    const coords::VecIdent *coords = coords_->makeCoordsForVecIdent(ast);
    domain::Identifier *dom = domain_->addIdentifier(space, coords);
    coords2dom_->putIdentifierInterp(coords, dom);

    cerr << "domain::Identifier *mkVecIdent: AST at " << std::hex << ast << "; Coords at " << std::hex << coords << ";  coords.toString is " << coords->toString() << "; dom at " << std::hex << dom << "\n";
    cerr << "END interp::VecIdent *addVecIdent\n";

    return dom;
}

void Interpretation::mkVecBinding(ast::Stmt *ast, domain::Identifier *id, domain::Expr *exp)
{
    cerr << "START: Interpretation::mkVecBinding.\n.";
    if (!exp || !id)
    {
        cerr << "Interpretation::mkVecBinding: null argument\n";
    }

    const coords::VecIdent *id_coords = id->getVarDeclWrapper();
    const coords::ExprASTNode *exp_coords = exp->getExprASTNode();
    coords::BindingASTNode *bind_coords = new coords::BindingASTNode(ast, id_coords, exp_coords);
    ast2coords_->stmt_wrappers.insert(std::make_pair(ast, bind_coords));
    domain::Binding &binding =
        domain_->addBinding(bind_coords, id, exp);
    coords2dom_->putBindingInterp(bind_coords, binding);

    cerr << 
        "Interpretation::mkVecBinding: identifier at " << 
        std::hex << id << 
        " wrapped addr is " << std::hex << id_coords->getASTNode() <<
        "\n";
    cerr << "Interpretation::mkVecBinding: wrapped dump is \n";
    id_coords->getASTNode()->dump();
    cerr << "Interpretation::mkVecBinding: name is " << id_coords->toString() << "\n";


    cerr << "DONE: Interpretation::mkVecBinding..\n";
}
