#ifndef ASTTOCOORDS_H
#define ASTTOCOORDS_H

#include "AST.h"
#include "clang/AST/AST.h"
#include "Coords.h"

namespace ast2coords {

class ASTToCoords {
public:
    const coords::VecIdent *makeCoordsForVecIdent(const ast::VecIdent *ident);
//    const coords::Coords *getCoords(ast::Expr* e);

// protected
// TODO: Use AST.h type aliases
// Note: All coords are coords::Coords
    void overrideExpr(const clang::Expr *e, const coords::Coords *c);
    void overrideStmt(const clang::Stmt *s, const coords::Coords *c);
    void overrideDecl(const clang::Decl *d, const coords::Coords *c);

// private
//
// TODO: Note and rethink: everything in coords is coords::Coords.
//
    std::unordered_map<const clang::Expr *, const coords::Coords *> expr_coords;
    std::unordered_map<const clang::Stmt *, const coords::Coords *> stmt_coords;
    std::unordered_map<const clang::Decl *, const coords::Coords *> decl_coords;
};

// TODO: Refactor to use AST.h abstractions

} // namespace

#endif