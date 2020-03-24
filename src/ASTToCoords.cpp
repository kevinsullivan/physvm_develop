#include "ASTToCoords.h"
//#include <g3log/g3log.hpp>

#include<iostream>
#include<exception>
#include<memory>

/*
Create Coords object for given AST node and update AST-to_Coords
mappings. Currently this means just the ast2coords unorderedmaps,
one for Clang AST objects inheriting from Stmt, and one for Clang
AST objects inheriting from Decl. We maintain both forward and
backwards maps. See AST.h for the translations.
*/
using namespace ast2coords;

ASTToCoords::ASTToCoords() {
   this->stmt_coords = new std::unordered_map<const clang::Stmt *, coords::Coords *>();
   this->decl_coords = new std::unordered_map<const clang::Decl *, coords::Coords *>();
   this->coords_stmt = new std::unordered_map<coords::Coords *,const clang::Stmt *>();
   this->coords_decl = new std::unordered_map<coords::Coords *,const clang::Decl *>();
}

/*

coords::VecParenExpr *ASTToCoords::mkVecParenExpr(ast::VecParenExpr *ast, clang::ASTContext *c, ast::VecExpr *expr) {
    coords::VecExpr *expr_coords = static_cast<coords::VecExpr*>(stmt_coords->at(expr));
    if (!expr_coords) {
        //LOG(FATAL) << "ASTToCoords::mkVecParenExpr: Error. No expr coords.\n"; 
    }
    coords::VecParenExpr *coord = new coords::VecParenExpr(ast, c, expr_coords); 
    overrideStmt2Coords(ast, coord); 
    overrideCoords2Stmt(coord, ast);
    return coord;  
}
*/

coords::VecWrapper *ASTToCoords::mkVecWrapper(const ast::ExprWithCleanupsWrapper *wrapper, clang::ASTContext *c, ast::VecExpr *expr){
    coords::VecExpr *expr_coords = static_cast<coords::VecExpr*>(stmt_coords->at(expr));
    
    coords::VecWrapper *coord = new coords::VecWrapper(wrapper, c, expr_coords);
    overrideStmt2Coords(wrapper, coord);
    overrideCoords2Stmt(coord, wrapper);

    return coord;
}

coords::VecWrapper *ASTToCoords::mkVecWrapper(const ast::ImplicitCastExprWrapper *wrapper, clang::ASTContext *c, ast::VecExpr *expr){
    coords::VecExpr *expr_coords = static_cast<coords::VecExpr*>(stmt_coords->at(expr));
    
    coords::VecWrapper *coord = new coords::VecWrapper(wrapper, c, expr_coords);
    overrideStmt2Coords(wrapper, coord);
    overrideCoords2Stmt(coord, wrapper);

    return coord;
}

coords::FloatWrapper *ASTToCoords::mkFloatWrapper(const ast::ExprWithCleanupsWrapper *wrapper, clang::ASTContext *c, ast::FloatExpr *expr){
    coords::FloatExpr *expr_coords = static_cast<coords::FloatExpr*>(stmt_coords->at(expr));
    
    coords::FloatWrapper *coord = new coords::FloatWrapper(wrapper, c, expr_coords);
    overrideStmt2Coords(wrapper, coord);
    overrideCoords2Stmt(coord, wrapper);

    return coord;
}

coords::FloatWrapper *ASTToCoords::mkFloatWrapper(const ast::ImplicitCastExprWrapper *wrapper, clang::ASTContext *c, ast::FloatExpr *expr){
    coords::FloatExpr *expr_coords = static_cast<coords::FloatExpr*>(stmt_coords->at(expr));
    
    coords::FloatWrapper *coord = new coords::FloatWrapper(wrapper, c, expr_coords);
    overrideStmt2Coords(wrapper, coord);
    overrideCoords2Stmt(coord, wrapper);

    return coord;
}

coords::VecIdent *ASTToCoords::mkVecIdent(const ast::VecIdent *ast, clang::ASTContext *c) {
    coords::VecIdent *coord = new coords::VecIdent(ast, c);
    //delete this->decl_coords;
    //if(this->decl_coords->size() == 0)
    //this->decl_coords = decl_coords = new std::unordered_map<const clang::Decl *, coords::Coords *>();
    //decl_coords->clear();
    //decl_coords->emplace(ast, coord);
    overrideDecl2Coords(ast,coord);     // Use Clang canonical addresses? 
    overrideCoords2Decl(coord, ast);     // Use Clang canonical addresses?  
    return coord;
}

coords::FloatIdent *ASTToCoords::mkFloatIdent(const ast::FloatIdent *ast, clang::ASTContext *c) {
    coords::FloatIdent *coord = new coords::FloatIdent(ast, c);
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

coords::FloatVarExpr *ASTToCoords::mkFloatVarExpr(const ast::FloatVarExpr *ast, clang::ASTContext *c) {
    coords::FloatVarExpr *coord = new coords::FloatVarExpr(ast, c);
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


coords::VecScalarMulExpr *ASTToCoords::mkVecScalarMulExpr(
       const ast::VecScalarMulExpr *ast, clang::ASTContext *c,
       coords::FloatExpr *flt, coords::VecExpr *vec 
    ){
    coords::VecScalarMulExpr *coord = new coords::VecScalarMulExpr(ast, c, flt, vec);
    overrideStmt2Coords(ast, coord);
    overrideCoords2Stmt(coord, ast);
    return coord;
}


coords::VecParenExpr *ASTToCoords::mkVecParenExpr(ast::VecParenExpr *ast, clang::ASTContext *c, ast::VecExpr *expr) {
    coords::VecExpr *expr_coords = static_cast<coords::VecExpr*>(stmt_coords->at(expr));
    if (!expr_coords) {
        //LOG(FATAL) << "ASTToCoords::mkVecParenExpr: Error. No expr coords.\n"; 
    }
    coords::VecParenExpr *coord = new coords::VecParenExpr(ast, c, expr_coords); 
    overrideStmt2Coords(ast, coord); 
    overrideCoords2Stmt(coord, ast);
    return coord;  
}


coords::FloatParenExpr *ASTToCoords::mkFloatParenExpr(ast::FloatParenExpr *ast, clang::ASTContext *c, ast::FloatExpr *expr) {
    coords::FloatExpr *expr_coords = static_cast<coords::FloatExpr*>(stmt_coords->at(expr));
    if (!expr_coords) {
        //LOG(FATAL) << "ASTToCoords::mkVecParenExpr: Error. No expr coords.\n"; 
    }
    coords::FloatParenExpr *coord = new coords::FloatParenExpr(ast, c, expr_coords); 
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

coords::Float_Lit *ASTToCoords::mkFloat_Lit(const ast::Float_Lit *ast, clang::ASTContext *c, ast::Scalar scalar) {
    coords::Float_Lit *coord = new coords::Float_Lit(ast, c, scalar); 
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

coords::Float_Var *ASTToCoords::mkFloat_Var(
        const ast::Float_Var *ast, clang::ASTContext *c, coords::FloatVarExpr *var_coords) {
    coords::Float_Var *coord = new coords::Float_Var(ast, c, var_coords);
    overrideStmt2Coords(ast,coord);
    overrideCoords2Stmt(coord,ast);
    return coord;
}




coords::Vector_Expr *ASTToCoords::mkVector_Expr(
        const ast::Vector_Expr *ctor_ast, clang::ASTContext *c, const ast::VecExpr *expr_ast) {
    coords::VecExpr *expr_coords = static_cast<coords::VecExpr*>(stmt_coords->at(expr_ast));
    coords::Vector_Expr *coord = new coords::Vector_Expr(ctor_ast, c, expr_coords);
    overrideStmt2Coords(ctor_ast,coord);
    overrideCoords2Stmt(coord,ctor_ast);
    return coord;    
}


coords::Float_Expr *ASTToCoords::mkFloat_Expr(
        const ast::Float_Expr *ctor_ast, clang::ASTContext *c, const ast::FloatExpr *expr_ast) {
    coords::FloatExpr *expr_coords = static_cast<coords::FloatExpr*>(stmt_coords->at(expr_ast));
    coords::Float_Expr *coord = new coords::Float_Expr(ctor_ast, c, expr_coords);
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


coords::Float_Def *ASTToCoords::mkFloat_Def(
        const ast::Float_Def *ast, clang::ASTContext *c, coords::FloatIdent *id_coords, coords::FloatExpr *flt_coords) {
    coords::Float_Def *coord = new coords::Float_Def(ast, c, id_coords, flt_coords);
    overrideStmt2Coords(ast,coord);
    overrideCoords2Stmt(coord, ast);
    return coord;
}



//using namespace std;
void ASTToCoords::overrideStmt2Coords(const clang::Stmt *s, coords::Coords *c) {
    stmt_coords->insert(std::make_pair(s, c));
}



void ASTToCoords::overrideDecl2Coords(const clang::Decl *d, coords::Coords *c) {
    
    decl_coords->insert(std::make_pair(d, c));
}



void ASTToCoords::overrideCoords2Stmt(coords::Coords *c, const clang::Stmt *s) {
    
    coords_stmt->insert(std::make_pair(c, s));
}



void ASTToCoords::overrideCoords2Decl(coords::Coords *c, const clang::Decl *d) {
    
    coords_decl->insert(std::make_pair(c, d));
}
