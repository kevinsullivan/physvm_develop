#include "ASTToCoords.h"

using namespace ast2coords;

// Create right coordinates object and "add to system" (update ast_to_coords map)
const coords::VecIdent *ASTToCoords::makeCoordsForVecIdent(const ast::VecIdent *ident) {
    coords::VecIdent *vecCoords = new coords::VecIdent(ident);
    overrideDecl(ident,vecCoords);                          // TO DO Canonicalize
    return vecCoords;
}

// TODO: Transition from clang to ast abstraction for rest of this file

void ASTToCoords::overrideExpr(const clang::Expr *e, const coords::VecExpr *c) {
    expr_coords.insert(std::make_pair(e, c));
}

void ASTToCoords::overrideStmt(const clang::Stmt *s, const coords::VecExpr *c) {
    stmt_coords.insert(std::make_pair(s, c));
}

void ASTToCoords::overrideDecl(const clang::Decl *d, const coords::VecExpr *c) {
    std::cerr << "ASTToCoords::overrideDecl: AST " << std::hex << d << "to coords " 
        << std::hex << c << " toString " << c->toString() << "\n";
    decl_coords.insert(std::make_pair(d, c));
}

const coords::VecExpr *ASTToCoords::getCoords(ast::Expr* e) {
    return expr_coords[e];
}