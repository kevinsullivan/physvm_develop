#ifndef ASTTOCOORDS_H
#define ASTTOCOORDS_H

#include "AST.h"
#include "clang/AST/AST.h"
#include "Coords.h"

namespace ast2coords {

class ASTToCoords {
public:
    const coords::VecIdent *makeCoordsForVecIdent(const ast::VecIdent *ident);
//    const coords::VecExpr *getCoords(ast::Expr* e);

// protected
// TODO: Use AST.h type aliases
// Note: All coords are coords::VecExpr
    void overrideExpr(const clang::Expr *e, const coords::VecExpr *c);
    void overrideStmt(const clang::Stmt *s, const coords::VecExpr *c);
    void overrideDecl(const clang::Decl *d, const coords::VecExpr *c);

// private
//
// TODO: Note and rethink: everything in coords is coords::VecExpr.
//
    std::unordered_map<const clang::Expr *, const coords::VecExpr *> expr_coords;
    std::unordered_map<const clang::Stmt *, const coords::VecExpr *> stmt_coords;
    std::unordered_map<const clang::Decl *, const coords::VecExpr *> decl_coords;
};

// TODO: Refactor to use AST.h abstractions

} // namespace

#endif