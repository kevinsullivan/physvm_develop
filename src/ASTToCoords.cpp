#include "ASTToCoords.h"
//#include <g3log/g3log.hpp>


/*
Create Coords object for given AST node and update AST-to_Coords
mappings. Currently this means just the ast2coords unorderedmaps,
one for Clang AST objects inheriting from Stmt, and one for Clang
AST objects inheriting from Decl. We maintain both forward and
backwards maps. See AST.h for the translations.
*/
using namespace ast2coords;

ASTToCoords::ASTToCoords() {}

coords::VecIdent *ASTToCoords::mkVecIdent(const ast::VecIdent *ast, clang::ASTContext *c) {
    coords::VecIdent *coord = new coords::VecIdent(ast, c);
    overrideDecl2Coords(ast,coord);     // Use Clang canonical addresses? 
    overrideCoords2Decl(coord, ast);     // Use Clang canonical addresses? 
    return coord;
}

coords::VecVarExpr *ASTToCoords::mkVecVarExpr(const ast::VecVarExpr *ast, clang::ASTContext *c) {
    coords::VecVarExpr *coord = new coords::VecVarExpr(ast, c);
    overrideStmt2Coords(ast, coord);   // DeclRefExpr is ako Stmt
    overrideCoords2Stmt(coord, ast);   // DeclRefExpr is ako Stmt
    return coord;
}

coords::VecVecAddExpr *ASTToCoords::mkVecVecAddExpr(
        const ast::VecVecAddExpr *ast, clang::ASTContext *c, 
        coords::VecExpr *mem, 
        coords::VecExpr *arg) {
    coords::VecVecAddExpr *coord = new coords::VecVecAddExpr(ast, c, mem,arg);
    overrideStmt2Coords(ast,coord);                          // TO DO Canonicalize
    overrideCoords2Stmt(coord, ast);                          // TO DO Canonicalize
    return coord;
}

coords::VecScalarMulExpr *ASTToCoords::mkVecScalarExpr(
       const ast::VecScalarMulExpr *ast, clang::ASTContext *c,
       coords::ScalarExpr *flt, coords::VecExpr *vec 
    ){
    coords::VecScalarMulExpr *coord = new coords::VecScalarMulExpr(ast, c, flt, vec);
    overrideStmt2Coords(ast, coord);
    overrideCoords2Stmt(coord, ast);
}

coords::VecParenExpr *ASTToCoords::mkVecParenExpr(ast::VecParenExpr *ast, clang::ASTContext *c, ast::VecExpr *expr) {
    coords::VecExpr *expr_coords = static_cast<coords::VecExpr*>(stmt_coords[expr]);
    if (!expr_coords) {
        //LOG(FATAL) << "ASTToCoords::mkVecParenExpr: Error. No expr coords.\n"; 
    }
    coords::VecParenExpr *coord = new coords::VecParenExpr(ast, c, expr_coords); 
    overrideStmt2Coords(ast, coord); 
    overrideCoords2Stmt(coord, ast);
    return coord;  
}
    

coords::Vector_Lit *ASTToCoords::mkVector_Lit(const ast::Vector_Lit *ast, clang::ASTContext *c, ast::Scalar x, ast::Scalar y, ast::Scalar z) {
    coords::Vector_Lit *coord = new coords::Vector_Lit(ast, c, x, y, z); 
    overrideStmt2Coords(ast,coord); 
    overrideCoords2Stmt(coord,ast); 
    return coord;
}

coords::Vector_Var *ASTToCoords::mkVector_Var(
        const ast::Vector_Var *ast, clang::ASTContext *c, coords::VecVarExpr *var_coords) {
    coords::Vector_Var *coord = new coords::Vector_Var(ast, c, var_coords);
    overrideStmt2Coords(ast,coord);
    overrideCoords2Stmt(coord,ast);
    return coord;
}


coords::Vector_Expr *ASTToCoords::mkVector_Expr(
        const ast::Vector_Expr *ctor_ast, clang::ASTContext *c, const ast::VecExpr *expr_ast) {
    coords::VecExpr *expr_coords = static_cast<coords::VecExpr*>(stmt_coords[expr_ast]);
    coords::Vector_Expr *coord = new coords::Vector_Expr(ctor_ast, c, expr_coords);
    overrideStmt2Coords(ctor_ast,coord);
    overrideCoords2Stmt(coord,ctor_ast);
    return coord;    
}

coords::Vector_Def *ASTToCoords::mkVector_Def(
        const ast::Vector_Def *ast, clang::ASTContext *c, coords::VecIdent *id_coords, coords::VecExpr *vec_coords) {
    coords::Vector_Def *coord = new coords::Vector_Def(ast, c, id_coords, vec_coords);
    overrideStmt2Coords(ast,coord);
    overrideCoords2Stmt(coord, ast);
    return coord;
}

void ASTToCoords::overrideStmt2Coords(const clang::Stmt *s, coords::Coords *c) {
    stmt_coords.insert(std::make_pair(s, c));
}

void ASTToCoords::overrideDecl2Coords(const clang::Decl *d, coords::Coords *c) {
    decl_coords.insert(std::make_pair(d, c));
}

void ASTToCoords::overrideCoords2Stmt(coords::Coords *c, const clang::Stmt *s) {
    coords_stmt.insert(std::make_pair(c, s));
}

void ASTToCoords::overrideCoords2Decl(coords::Coords *c, const clang::Decl *d) {
    coords_decl.insert(std::make_pair(c, d));
}
