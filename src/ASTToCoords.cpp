#include "ASTToCoords.h"


/*
Create Coords object for given AST node and update AST-to_Coords
mappings. Currently this means just the ast2coords unorderedmaps,
one for Clang AST objects inheriting from Stmt, and one for Clang
AST objects inheriting from Decl. See AST.h for the translations.
TODO: Consider making Clang AST types visible in type signatures. 
*/
using namespace ast2coords;

ASTToCoords::ASTToCoords() {}

coords::VecIdent *ASTToCoords::mkVecIdent(const ast::VecIdent *ast) {
    coords::VecIdent *coord = new coords::VecIdent(ast);
    overrideDecl2Coords(ast,coord);     // Use Clang canonical addresses? 
    overrideCoords2Decl(coord, ast);     // Use Clang canonical addresses? 
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
    coords::VecVarExpr *coord = new coords::VecVarExpr(ast);
    overrideStmt2Coords(ast, coord);   // DeclRefExpr is ako Stmt
    overrideCoords2Stmt(coord, ast);   // DeclRefExpr is ako Stmt
    return coord;
}

/*
coords::VecVarExpr *ASTToCoords::mkVecVarExpr(const ast::VecVarExpr *ast) {
    coords::VecVarExpr *c = new coords::VecVarExpr(ast);
    overrideStmt(ast,c);                          // TO DO Canonicalize
    return c;
}
*/

coords::VecVecAddExpr *ASTToCoords::mkVecVecAddExpr(
        const ast::VecVecAddExpr *ast, 
        coords::VecExpr *mem, 
        coords::VecExpr *arg) {
    coords::VecVecAddExpr *coord = new coords::VecVecAddExpr(ast,mem,arg);
    overrideStmt2Coords(ast,coord);                          // TO DO Canonicalize
    overrideCoords2Stmt(coord, ast);                          // TO DO Canonicalize
    return coord;
}

    
/*coords::Vector *ASTToCoords::Vector(const ast::Vector *ast) {
    coords::Vector *c = new coords::Vector(ast);
    overrideStmt(ast,coord);                          // TO DO Canonicalize
    return coord;
}*/

// Assume 1-d space
coords::Vector_Lit *ASTToCoords::mkVector_Lit(const ast::Vector_Lit *ast, ast::Scalar x, ast::Scalar y, ast::Scalar z) {
    // TODO: Abstracted coords from actual code 
    coords::Vector_Lit *coord = new coords::Vector_Lit(ast, x, y, z); 
    overrideStmt2Coords(ast,coord); 
    overrideCoords2Stmt(coord,ast); 
    return coord;
}

coords::Vector_Var *ASTToCoords::mkVector_Var(
        const ast::Vector_Var *ast, coords::VecVarExpr *var_coords) {
    coords::Vector_Var *coord = new coords::Vector_Var(ast, var_coords);
    overrideStmt2Coords(ast,coord);
    overrideCoords2Stmt(coord,ast);
    return coord;
}


coords::Vector_Expr *ASTToCoords::mkVector_Expr(
        const ast::Vector_Expr *ctor_ast, const ast::VecExpr *expr_ast) {
    coords::VecExpr *expr_coords = static_cast<coords::VecExpr*>(stmt_coords[expr_ast]);
    coords::Vector_Expr *coord = new coords::Vector_Expr(ctor_ast, expr_coords);
    overrideStmt2Coords(ctor_ast,coord);
    overrideCoords2Stmt(coord,ctor_ast);
    return coord;    
}


// TO DO : VECTOR_DEF

coords::Vector_Def *ASTToCoords::mkVector_Def(
        const ast::Vector_Def *ast, coords::VecIdent *id_coords, coords::VecExpr *vec_coords) {
    coords::Vector_Def *coord = new coords::Vector_Def(ast, id_coords, vec_coords);
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
