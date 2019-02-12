#ifndef CODETOCOORDS_H
#define CODETOCOORDS_H

class CodeToCoords {
public:
    void overrideExpr(const clang::Expr *e, const coords::ExprASTNode *c) {
    }
    void overrideStmt(const clang::Stmt *e, const coords::ExprASTNode *c) {
    }
    void overrideDecl(const clang::Decl *e, const coords::ExprASTNode *c) {
    }

    unordered_map<const clang::Expr *, const coords::ExprASTNode *> expr_wrappers;
    unordered_map<const clang::Stmt *, const coords::ExprASTNode *> stmt_wrappers;
    unordered_map<const clang::Decl *, const coords::ExprASTNode *> decl_wrappers;
};

#endif