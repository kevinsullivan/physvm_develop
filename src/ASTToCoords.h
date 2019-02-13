#ifndef ASTTOCOORDS_H
#define ASTTOCOORDS_H

#include "clang/AST/AST.h"
#include "AST.h"

namespace ast2coords {

class ASTToCoords {
public:

    const VecIdent *makeCoordsForVecIdent(const ast::Ident *ident);

// protected
// TODO: Use AST.h type aliases
//
    void overrideExpr(const clang::Expr *e, const coords::ExprASTNode *c);
    void overrideStmt(const clang::Stmt *s, const coords::ExprASTNode *c);
    void overrideDecl(const clang::Decl *d, const coords::ExprASTNode *c);
    const coords::ExprASTNode *getASTExprCoords(ast::Expr* e);

// private
    unordered_map<const clang::Expr *, const coords::ExprASTNode *> expr_coords;
    unordered_map<const clang::Stmt *, const coords::ExprASTNode *> stmt_coords;
    unordered_map<const clang::Decl *, const coords::ExprASTNode *> decl_coords;
};

// TODO: Refactor to use AST.h abstractions

} // namespace

#endif