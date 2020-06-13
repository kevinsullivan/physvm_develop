#include "ASTToCoords.h"
#include <g3log/g3log.hpp>

#include<iostream>
#include<exception>
#include<memory>
#include<string>

#include "llvm/Support/Casting.h"
/*
Create Coords object for given AST node and update AST-to_Coords
mappings. Currently this means just the ast2coords unorderedmaps,
one for Clang AST objects inheriting from Stmt, and one for Clang
AST objects inheriting from Decl. We maintain both forward and
backwards maps. See AST.h for the translations.
*/
using namespace ast2coords;

void ASTToCoords::setASTState(coords::Coords *coords, clang::Stmt* stmt, clang::ASTContext *c){
    auto range = stmt->getSourceRange();
    auto begin = c->getFullLoc(range.getBegin());
    auto end = c->getFullLoc(range.getEnd());

    coords->state_ = new coords::ASTState(
        "",
        "",
        "",
        (clang::dyn_cast<ast::VecVarExpr>(stmt)) ? (clang::dyn_cast<ast::VecVarExpr>(stmt))->getDecl()->getNameAsString() : 
        (clang::dyn_cast<ast::ScalarVarExpr>(stmt)) ? (clang::dyn_cast<ast::ScalarVarExpr>(stmt))->getDecl()->getNameAsString() : "",
        begin.getSpellingLineNumber(),
        begin.getSpellingColumnNumber(),
        end.getSpellingLineNumber(),
        end.getSpellingColumnNumber()
    );
    /*
    coords->state_.file_id_ = new std::string("");
    coords->state_.file_name_ = "";
    coords->state_.file_path_ = "";

    coords->state_.name_ = 
        ((ast::VecVarExpr*) stmt) ? ((ast::VecVarExpr*) stmt)->getDecl()->getNameAsString() : 
        ((ast::ScalarVarExpr*) stmt) ? ((ast::ScalarVarExpr*) stmt)->getDecl()->getNameAsString() : "";

    
    coords->state_.begin_line_no_ = begin.getSpellingLineNumber();
    coords->state_.begin_col_no_ = begin.getSpellingColumnNumber();
    coords->state_.end_line_no_ = end.getSpellingLineNumber();
    coords->state_.end_col_no_ = end.getSpellingColumnNumber();
    */
}

void ASTToCoords::setASTState(coords::Coords *coords, clang::Decl* decl, clang::ASTContext *c){
    auto range = decl->getSourceRange();
    auto begin = c->getFullLoc(range.getBegin());
    auto end = c->getFullLoc(range.getEnd());

    coords->state_ = new coords::ASTState(
        "",
        "",
        "",
        (clang::dyn_cast<ast::VecIdent>(decl)) ? (clang::dyn_cast<ast::VecIdent>(decl))->getNameAsString() : 
        (clang::dyn_cast<ast::ScalarIdent>(decl)) ? (clang::dyn_cast<ast::ScalarIdent>(decl))->getNameAsString() : "",
        begin.getSpellingLineNumber(),
        begin.getSpellingColumnNumber(),
        end.getSpellingLineNumber(),
        end.getSpellingColumnNumber()
    );
    /*
    coords->state_.file_id_ = "";
    coords->state_.file_name_ = "";
    coords->state_.file_path_ = "";

    coords->state_.name_ = ((clang::NamedDecl*) decl) ? ((clang::NamedDecl*) decl)->getNameAsString() : "";

    coords->state_.begin_line_no_ = begin.getSpellingLineNumber();
    coords->state_.begin_col_no_ = begin.getSpellingColumnNumber();
    coords->state_.end_line_no_ = end.getSpellingLineNumber();
    coords->state_.end_col_no_ = end.getSpellingColumnNumber();
    */
}

ASTToCoords::ASTToCoords() {
   this->stmt_coords = new std::unordered_map<const clang::Stmt *, coords::Coords *>();
   this->decl_coords = new std::unordered_map<const clang::Decl *, coords::Coords *>();
   this->coords_stmt = new std::unordered_map<coords::Coords *,const clang::Stmt *>();
   this->coords_decl = new std::unordered_map<coords::Coords *,const clang::Decl *>();
}

coords::VecIdent *ASTToCoords::mkVecIdent(const ast::VecIdent *ast, clang::ASTContext *c) {
    coords::VecIdent *coord = new coords::VecIdent();
    if(clang::isa<clang::Decl>(ast))
        setASTState(coord, const_cast<clang::Decl*>(clang::dyn_cast<clang::Decl>(ast)), c);
    overrideDecl2Coords(ast,coord);     // Use Clang canonical addresses? 
    overrideCoords2Decl(coord, ast);     // Use Clang canonical addresses?  
    return coord;
}

coords::ScalarIdent *ASTToCoords::mkScalarIdent(const ast::ScalarIdent *ast, clang::ASTContext *c) {
    coords::ScalarIdent *coord = new coords::ScalarIdent();
    if(clang::isa<clang::Decl>(ast))
        setASTState(coord, const_cast<clang::Decl*>(clang::dyn_cast<clang::Decl>(ast)), c);
    overrideDecl2Coords(ast,coord);     // Use Clang canonical addresses? 
    overrideCoords2Decl(coord, ast);     // Use Clang canonical addresses? 
    return coord;
}

coords::TransformIdent *ASTToCoords::mkTransformIdent(const ast::TransformIdent *ast, clang::ASTContext *c) {
    coords::TransformIdent *coord = new coords::TransformIdent();
    if(clang::isa<clang::Decl>(ast))
        setASTState(coord, const_cast<clang::Decl*>(clang::dyn_cast<clang::Decl>(ast)), c);
    overrideDecl2Coords(ast,coord);     // Use Clang canonical addresses? 
    overrideCoords2Decl(coord, ast);     // Use Clang canonical addresses? 
    return coord;
}

coords::VecVarExpr *ASTToCoords::mkVecVarExpr(const ast::VecVarExpr *ast, clang::ASTContext *c) {
    coords::VecVarExpr *coord = new coords::VecVarExpr();
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast, coord);   // DeclRefExpr is ako Stmt
    overrideCoords2Stmt(coord, ast);   // DeclRefExpr is ako Stmt
    return coord;
}

coords::ScalarVarExpr *ASTToCoords::mkScalarVarExpr(const ast::ScalarVarExpr *ast, clang::ASTContext *c) {
    coords::ScalarVarExpr *coord = new coords::ScalarVarExpr();
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast, coord);   // DeclRefExpr is ako Stmt
    overrideCoords2Stmt(coord, ast);   // DeclRefExpr is ako Stmt
    return coord;
}

coords::TransformVarExpr *ASTToCoords::mkTransformVarExpr(const ast::TransformVarExpr *ast, clang::ASTContext *c) {
    coords::TransformVarExpr *coord = new coords::TransformVarExpr();
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast, coord);   // DeclRefExpr is ako Stmt
    overrideCoords2Stmt(coord, ast);   // DeclRefExpr is ako Stmt
    return coord;
}




coords::VecVecAddExpr *ASTToCoords::mkVecVecAddExpr(
        const ast::VecVecAddExpr *ast, clang::ASTContext *c, 
        coords::VecExpr *mem, 
        coords::VecExpr *arg) {
    coords::VecVecAddExpr *coord = new coords::VecVecAddExpr(mem,arg);
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast,coord);                          // TO DO Canonicalize
    overrideCoords2Stmt(coord, ast);                          // TO DO Canonicalize
    return coord;
}


coords::VecScalarMulExpr *ASTToCoords::mkVecScalarMulExpr(
       const ast::VecScalarMulExpr *ast, clang::ASTContext *c,
       coords::ScalarExpr *flt, coords::VecExpr *vec 
    ){
    coords::VecScalarMulExpr *coord = new coords::VecScalarMulExpr(flt, vec);
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast, coord);
    overrideCoords2Stmt(coord, ast);
    return coord;
}


coords::TransformVecApplyExpr *ASTToCoords::mkTransformVecApplyExpr(ast::TransformVecApplyExpr *ast, coords::TransformExpr *texpr, coords::VecExpr *vexpr, clang::ASTContext *c){
    coords::TransformVecApplyExpr *coord = new coords::TransformVecApplyExpr(texpr, vexpr);
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast, coord);
    overrideCoords2Stmt(coord, ast);
    return coord;
}

coords::ScalarScalarAddExpr *ASTToCoords::mkScalarScalarAddExpr(
        const ast::ScalarScalarAddExpr *ast, clang::ASTContext *c, 
        coords::ScalarExpr *lhs, 
        coords::ScalarExpr *rhs) {
    coords::ScalarScalarAddExpr *coord = new coords::ScalarScalarAddExpr(lhs,rhs);
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast,coord);                          // TO DO Canonicalize
    overrideCoords2Stmt(coord, ast);                          // TO DO Canonicalize
    return coord;
}

coords::ScalarScalarMulExpr *ASTToCoords::mkScalarScalarMulExpr(
        const ast::ScalarScalarMulExpr *ast, clang::ASTContext *c, 
        coords::ScalarExpr *lhs, 
        coords::ScalarExpr *rhs) {
    coords::ScalarScalarMulExpr *coord = new coords::ScalarScalarMulExpr(lhs,rhs);
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast,coord);                          // TO DO Canonicalize
    overrideCoords2Stmt(coord, ast);                          // TO DO Canonicalize
    return coord;
}

coords::TransformTransformComposeExpr *ASTToCoords::mkTransformTransformComposeExpr(ast::TransformTransformComposeExpr *ast, coords::TransformExpr *outer, coords::TransformExpr *inner, clang::ASTContext *c) {
    coords::TransformTransformComposeExpr *coord = new coords::TransformTransformComposeExpr(outer,inner);
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast,coord);                          // TO DO Canonicalize
    overrideCoords2Stmt(coord, ast);                          // TO DO Canonicalize
    return coord;
}


coords::VecParenExpr *ASTToCoords::mkVecParenExpr(ast::VecParenExpr *ast, clang::ASTContext *c, ast::VecExpr *expr) {
    coords::VecExpr *expr_coords = static_cast<coords::VecExpr*>(stmt_coords->at(expr));
    if (!expr_coords) {
        LOG(FATAL) << "ASTToCoords::mkVecParenExpr: Error. No expr coords.\n"; 
    }
    coords::VecParenExpr *coord = new coords::VecParenExpr(expr_coords); 
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast, coord); 
    overrideCoords2Stmt(coord, ast);
    return coord;  
}


coords::ScalarParenExpr *ASTToCoords::mkScalarParenExpr(ast::ScalarParenExpr *ast, clang::ASTContext *c, ast::ScalarExpr *expr) {
    coords::ScalarExpr *expr_coords = static_cast<coords::ScalarExpr*>(stmt_coords->at(expr));
    if (!expr_coords) {
        LOG(FATAL) << "ASTToCoords::mkScalarParenExpr: Error. No expr coords.\n"; 
    }
    coords::ScalarParenExpr *coord = new coords::ScalarParenExpr(expr_coords); 
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast, coord); 
    overrideCoords2Stmt(coord, ast);
    return coord;  
} 


coords::TransformParenExpr *ASTToCoords::mkTransformParenExpr(ast::TransformParenExpr *ast, ast::TransformExpr *expr, clang::ASTContext *c) {
    coords::TransformExpr *expr_coords = static_cast<coords::TransformExpr*>(stmt_coords->at(expr));
    if (!expr_coords) {
        LOG(FATAL) << "ASTToCoords::mkTransformParenExpr: Error. No expr coords.\n"; 
    }
    coords::TransformParenExpr *coord = new coords::TransformParenExpr(expr_coords); 
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast, coord); 
    overrideCoords2Stmt(coord, ast);
    return coord;  
}       


coords::Vector_Lit *ASTToCoords::mkVector_Lit(const ast::Vector_Lit *ast, clang::ASTContext *c, ast::ScalarValue x, ast::ScalarValue y, ast::ScalarValue z) {
    coords::Vector_Lit *coord = new coords::Vector_Lit(); 
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast,coord); 
    overrideCoords2Stmt(coord,ast); 
    return coord;
}

coords::Scalar_Lit *ASTToCoords::mkScalar_Lit(const ast::Scalar_Lit *ast, clang::ASTContext *c, ast::ScalarValue scalar) {
    coords::Scalar_Lit *coord = new coords::Scalar_Lit(); 
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast,coord); 
    overrideCoords2Stmt(coord,ast); 
    return coord;
}

coords::Transform_Lit *ASTToCoords::mkTransform_Lit(const ast::Transform_Lit *ast, coords::VecExpr* arg1, coords::VecExpr* arg2, coords::VecExpr* arg3, clang::ASTContext *c) {
    coords::Transform_Lit *coord = new coords::Transform_Lit(arg1, arg2, arg3); 
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast,coord); 
    overrideCoords2Stmt(coord,ast); 
    return coord;
}

coords::Vector_Var *ASTToCoords::mkVector_Var(
        const ast::Vector_Var *ast, clang::ASTContext *c, coords::VecVarExpr *var_coords) {
    coords::Vector_Var *coord = new coords::Vector_Var(var_coords);
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast,coord);
    overrideCoords2Stmt(coord,ast);
    return coord;
}

coords::Scalar_Var *ASTToCoords::mkScalar_Var(
        const ast::Scalar_Var *ast, clang::ASTContext *c, coords::ScalarVarExpr *var_coords) {
    coords::Scalar_Var *coord = new coords::Scalar_Var(var_coords);
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast,coord);
    overrideCoords2Stmt(coord,ast);
    return coord;
}

coords::Transform_Var *ASTToCoords::mkTransform_Var(
        const ast::Transform_Var *ast, coords::TransformVarExpr *var_coords, clang::ASTContext *c) {
    coords::Transform_Var *coord = new coords::Transform_Var(var_coords);
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast,coord);
    overrideCoords2Stmt(coord,ast);
    return coord;
}




coords::Vector_Expr *ASTToCoords::mkVector_Expr(
        const ast::Vector_Expr *ctor_ast, clang::ASTContext *c, const ast::VecExpr *expr_ast) {
    coords::VecExpr *expr_coords = static_cast<coords::VecExpr*>(stmt_coords->at(expr_ast));
    coords::Vector_Expr *coord = new coords::Vector_Expr(expr_coords);
    if(clang::isa<clang::Stmt>(ctor_ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ctor_ast)), c);
    overrideStmt2Coords(ctor_ast,coord);
    overrideCoords2Stmt(coord,ctor_ast);
    return coord;    
}


coords::Scalar_Expr *ASTToCoords::mkScalar_Expr(
        const ast::Scalar_Expr *ctor_ast, clang::ASTContext *c, const ast::ScalarExpr *expr_ast) {
    coords::ScalarExpr *expr_coords = static_cast<coords::ScalarExpr*>(stmt_coords->at(expr_ast));
    coords::Scalar_Expr *coord = new coords::Scalar_Expr(expr_coords);
    if(clang::isa<clang::Stmt>(ctor_ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ctor_ast)), c);
    overrideStmt2Coords(ctor_ast,coord);
    overrideCoords2Stmt(coord,ctor_ast);
    return coord;    
}


coords::Transform_Expr *ASTToCoords::mkTransform_Expr(
        const ast::Transform_Expr *ctor_ast, const ast::TransformExpr *expr_ast, clang::ASTContext *c) {
    coords::TransformExpr *expr_coords = static_cast<coords::TransformExpr*>(stmt_coords->at(expr_ast));
    coords::Transform_Expr *coord = new coords::Transform_Expr(expr_coords);
    if(clang::isa<clang::Stmt>(ctor_ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ctor_ast)), c);
    overrideStmt2Coords(ctor_ast,coord);
    overrideCoords2Stmt(coord,ctor_ast);
    return coord;    
}



coords::Vector_Def *ASTToCoords::mkVector_Def(
        const ast::Vector_Def *ast, clang::ASTContext *c, coords::VecIdent *id_coords, coords::VecExpr *vec_coords) {
    coords::Vector_Def *coord = new coords::Vector_Def(id_coords, vec_coords);
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast,coord);
    overrideCoords2Stmt(coord, ast);
    return coord;
}


coords::Scalar_Def *ASTToCoords::mkScalar_Def(
        const ast::Scalar_Def *ast, clang::ASTContext *c, coords::ScalarIdent *id_coords, coords::ScalarExpr *flt_coords) {
    coords::Scalar_Def *coord = new coords::Scalar_Def(id_coords, flt_coords);
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast,coord);
    overrideCoords2Stmt(coord, ast);
    return coord;
}


coords::Transform_Def *ASTToCoords::mkTransform_Def(
        const ast::Transform_Def *ast, clang::ASTContext *c, coords::TransformIdent *id_coords, coords::TransformExpr *flt_coords) {
    coords::Transform_Def *coord = new coords::Transform_Def(id_coords, flt_coords);
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast,coord);
    overrideCoords2Stmt(coord, ast);
    return coord;
}

coords::Vector_Assign *ASTToCoords::mkVector_Assign(
        const ast::Vector_Assign *ast, clang::ASTContext *c, coords::VecVarExpr *var_coords, coords::VecExpr *vec_coords) {
    coords::Vector_Assign *coord = new coords::Vector_Assign(var_coords, vec_coords);
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast,coord);
    overrideCoords2Stmt(coord, ast);
    return coord;
}


coords::Scalar_Assign *ASTToCoords::mkScalar_Assign(
        const ast::Scalar_Assign *ast, clang::ASTContext *c, coords::ScalarVarExpr *var_coords, coords::ScalarExpr *flt_coords) {
    coords::Scalar_Assign *coord = new coords::Scalar_Assign(var_coords, flt_coords);
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
    overrideStmt2Coords(ast,coord);
    overrideCoords2Stmt(coord, ast);
    return coord;
}


coords::Transform_Assign *ASTToCoords::mkTransform_Assign(
        const ast::Transform_Assign *ast, clang::ASTContext *c, coords::TransformVarExpr *var_coords, coords::TransformExpr *flt_coords) {
    coords::Transform_Assign *coord = new coords::Transform_Assign(var_coords, flt_coords);
    if(clang::isa<clang::Stmt>(ast))
        setASTState(coord, const_cast<clang::Stmt*>(clang::dyn_cast<clang::Stmt>(ast)), c);
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
