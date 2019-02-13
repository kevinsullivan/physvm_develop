#include "ASTToCoords.h"

// Create right coordinates object and "add to system" (update ast_to_coords map)
const coords::VecIdent *ASTToCoords::makeCoordsForVecIdent(const ast::Ident *ident) {
    VecIdent *vecCoords = new coords::VecIdent(ident);
    overrideDecl(ident,vecCoords);                          // TO DO Canonicalize
    return vecCoords;
}


void ASTToCoords::overrideExpr(const clang::Expr *e, const coords::ExprASTNode *c) {
    expr_coords.insert(std::make_pair(e, c));
}

void ASTToCoords::overrideStmt(const clang::Stmt *s, const coords::ExprASTNode *c) {
    stmt_coords.insert(std::make_pair(s, c));
}

void ASTToCoords::overrideDecl(const clang::Decl *d, const coords::ExprASTNode *c) {
    cerr << "ASTToCoords::overrideDecl: AST " << std::hex << ident << "to coords " 
        << std::hex << vecCoords << " toString " << vecCoords->toString() << "\n";
    decl_coords.insert(std::make_pair(d, c));
}

const coords::ExprASTNode *ASTToCoords::getASTExprCoords(ast::Expr* e) {
    return expr_coords[e];
}

ASTToCoords.cpp:4:25: error: 'ASTToCoords' has not been declared
 const coords::VecIdent *ASTToCoords::makeCoordsForVecIdent(const ast::Ident *ident) {
