#ifndef CODETOCOORDS_H
#define CODETOCOORDS_H

class CodeToCoords {
public:
    void overrideExpr(const clang::Expr *e, const ExprASTNode *c) {
    }
    void overrideStmt(const clang::Stmt *e, const ExprASTNode *c) {
    }
    void overrideDecl(const clang::Decl *e, const ExprASTNode *c) {
    }

    unordered_map<const clang::Expr *, const ExprASTNode *> expr_wrappers;
    unordered_map<const clang::Stmt *, const ExprASTNode *> stmt_wrappers;
    unordered_map<const clang::Decl *, const ExprASTNode *> decl_wrappers;
};

#endif