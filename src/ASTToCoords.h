#ifndef ASTTOCOORDS_H
#define ASTTOCOORDS_H

#include "AST.h"
#include "clang/AST/AST.h"
#include "Coords.h"

#include <memory>

#include <iostream>

// KEVIN: For VecParenExpr module
#include "VecParenExpr.h"

/*
This relational class maps Clang AST nodes to code coordinates
in our ontology. We want a single base type for all coordinates. 
Clang does not have a single base type for all AST nodes. This is
a special case of the broader reality that we will want to have
code coordinates for diverse types of code elements. So we will
need multiple function types, from various code element types to
our uniform (base class for) code coordinates. Coords subclasses
add specialized state and behavior corresponding to their concrete
code element types.

Note: At present, the only kind of Clang AST nodes that we need
are Stmt nodes. Stmt is a deep base class for Clang AST nodes,
including clang::Expr, clang::DeclRefExpr, clang:MemberCallExpr,
and so forth. So the current class is overbuilt in a sense; but
we design it as we have to show the intended path to generality.

To use this class, apply the mk methods to Clang AST nodes of 
the appropriate types. These methods create Coord objects of the
corresponding types, wrape the AST nodes in the Coords objects,
update the relational map, and return the constructed Coords. 
Client code is responsible for deleting (TBD).

Also note that Vector_Lit doesn't have a sub-expression.
*/

namespace ast2coords {

/*
When generating interpretation, we know subtypes of vector expressions
(literal, variable, function application), and so do not need and should
not use a generic putter. So here there are no superclass mkVecExpr or
Vector mk oprations. 
*/

class ASTToCoords {
public:

    ASTToCoords();

    coords::VecIdent* mkVecIdent(const ast::VecIdent *ast, clang::ASTContext *c);
    // no VecExpr because we always know exactly what subtype we're creating
    coords::VecVarExpr* mkVecVarExpr(const ast::VecVarExpr *ast, clang::ASTContext *c);

    coords::VecVecAddExpr* mkVecVecAddExpr(const ast::VecVecAddExpr *ast, clang::ASTContext *c, 
                                             coords::VecExpr *mem, 
                                             coords::VecExpr *arg);

    coords::VecScalarMulExpr* mkVecScalarMulExpr(const ast::VecScalarMulExpr *ast, clang::ASTContext *c,
                                             coords::FloatExpr *flt, coords::VecExpr *vec);


    coords::FloatFloatAddExpr* mkFloatFloatAddExpr(const ast::FloatFloatAddExpr *ast, clang::ASTContext *c, 
                                             coords::FloatExpr *lhs, 
                                             coords::FloatExpr *rhs);

    coords::FloatFloatMulExpr* mkFloatFloatMulExpr(const ast::FloatFloatMulExpr *ast, clang::ASTContext *c, 
                                             coords::FloatExpr *lhs, 
                                             coords::FloatExpr *rhs);


    // KEVIN: Added for new horizontal vector paren expr module
    coords::VecParenExpr *mkVecParenExpr(ast::VecParenExpr *ast, clang::ASTContext *c,
                                                ast::VecExpr *expr);

    coords::Vector_Lit *mkVector_Lit(const ast::Vector_Lit *ast, clang::ASTContext *c,
                                                ast::Scalar x, ast::Scalar y, ast::Scalar z);
    coords::Vector_Var* mkVector_Var(const ast::Vector_Var *ast, clang::ASTContext *c,
                                                coords::VecVarExpr *var);
    coords::Vector_Expr* mkVector_Expr(const ast::Vector_Expr *ctor_ast, clang::ASTContext *c,
                                             ast::VecExpr *expr_ast);
    coords::Vector_Def* mkVector_Def(const ast::Vector_Def *ast, clang::ASTContext *c,
                                             coords::VecIdent *id, 
                                             coords::VecExpr *vec);

    coords::FloatIdent* mkFloatIdent(const ast::FloatIdent *ast, clang::ASTContext *c);
    // no VecExpr because we always know exactly what subtype we're creating
    coords::FloatVarExpr* mkFloatVarExpr(const ast::FloatVarExpr *ast, clang::ASTContext *c);

    // KEVIN: Added for new horizontal vector paren expr module
    coords::FloatParenExpr *mkFloatParenExpr(ast::FloatParenExpr *ast, clang::ASTContext *c,
                                                ast::FloatExpr *expr);

    coords::Float_Lit *mkFloat_Lit(const ast::Float_Lit *ast, clang::ASTContext *c,
                                                ast::Scalar scalar);
    coords::Float_Var* mkFloat_Var(const ast::Float_Var *ast, clang::ASTContext *c,
                                                coords::FloatVarExpr *var);
    coords::Float_Expr* mkFloat_Expr(const ast::Float_Expr *ctor_ast, clang::ASTContext *c,
                                             ast::FloatExpr *expr_ast);
    coords::Float_Def* mkFloat_Def(const ast::Float_Def *ast, clang::ASTContext *c,
                                             coords::FloatIdent *id, 
                                             coords::FloatExpr *flt);


    // TODO -- Have these routines return more specific subclass objects
    coords::Coords *getStmtCoords(const clang::Stmt *s) {
        auto dl = stmt_coords->find(s);

        return stmt_coords->find(s)->second;
    }

    coords::Coords *getDeclCoords(const clang::Decl *d) {
        auto dl = decl_coords->find(d);

        return dl->second;
    }

  private:
    void overrideStmt2Coords(const clang::Stmt *s, coords::Coords *c);
    void overrideDecl2Coords(const clang::Decl*, coords::Coords *c);
    void overrideCoords2Stmt(coords::Coords *c, const clang::Stmt *s);
    void overrideCoords2Decl(coords::Coords *c, const clang::Decl *d);
    /*
    std::unordered_map<const clang::Stmt *, coords::Coords *> stmt_coords;
    std::unordered_map<const clang::Decl *, coords::Coords *> decl_coords;
    std::unordered_map<coords::Coords *,const clang::Stmt *> coords_stmt;
    std::unordered_map<coords::Coords *,const clang::Decl *> coords_decl;
    */
    std::unordered_map<const clang::Stmt *, coords::Coords *> *stmt_coords;
    std::unordered_map<const clang::Decl *, coords::Coords *> *decl_coords;
    std::unordered_map<coords::Coords *,const clang::Stmt *> *coords_stmt;
    std::unordered_map<coords::Coords *,const clang::Decl *> *coords_decl;
    
};

} // namespace

#endif