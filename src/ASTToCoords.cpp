#include "ASTToCoords.h"

using namespace ast2coords;

coords::VecIdent *ASTToCoords::mkVecIdent(const ast::VecIdent *ast) {
    coords::VecIdent *coord = new coords::VecIdent(ast);
    overrideDecl(ast,coord);                          // TO DO Canonicalize
    return coord;
}

/* coords::VecExpr *ASTToCoords::mkVecExpr(const ast::VecExpr *ast) {
    coords::VecExpr *c = new coords::VecExpr(ast);
    overrideStmt(ast,coord);                          // TO DO Canonicalize
    return coord;
}*/

/*coords::VecLitExpr *ASTToCoords::mkVecLitExpr(const ast::VecLitExpr *ast) {
    coords::VecLitExpr *c = new coords::VecLitExpr(ast);
    overrideStmt(ast,coord);                          // TO DO Canonicalize
    return coord;
}*/

coords::VecVarExpr *ASTToCoords::mkVecVarExpr(const ast::VecVarExpr *ast) {
    coords::VecVarExpr *c = new coords::VecVarExpr(ast);
    overrideStmt(ast,c);                          // TO DO Canonicalize
    return c;
}

coords::VecVecAddExpr *ASTToCoords::mkVecVecAddExpr(const ast::VecVecAddExpr *ast, const coords::VecExpr *mem, const coords::VecExpr *arg) {
    coords::VecVecAddExpr *c = new coords::VecVecAddExpr(ast,mem,arg);
    overrideStmt(ast,c);                          // TO DO Canonicalize
    return coord;
}

coords::Vector *ASTToCoords::Vector(const ast::Vector *ast) {
    coords::Vector *c = new coords::Vector(ast);
    overrideStmt(ast,coord);                          // TO DO Canonicalize
    return coord;
}

coords::Vector_Lit *ASTToCoords::mkVector_Lit(const ast::Vector_Lit *ast) {
    coords::Vector_Lit *c = new coords::Vector_Lit(ast);
    overrideStmt(ast,coord);                          // TO DO Canonicalize
    return coord;
}

coords::Vector_Var *ASTToCoords::mkVector_Var(const ast::Vector_Var *ast) {
    coords::Vector_Var *c = new coords::Vector_Var(ast);
    overrideStmt(ast,coord);                          // TO DO Canonicalize
    return coord;
}

coords::Vector_Expr *ASTToCoords::mkVector_Expr(const ast::Vector_Expr *ast) {
    coords::Vector_Expr *c = new coords::Vector_Expr(ast);
    overrideStmt(ast,coord);                          // TO DO Canonicalize
    return coord;    
}
