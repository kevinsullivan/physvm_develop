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

    void setASTState(coords::Coords *coords, clang::Stmt* stmt, clang::ASTContext *c);
    void setASTState(coords::Coords *coords, clang::Decl* decl, clang::ASTContext *c);

    coords::VecIdent* mkVecIdent(const ast::VecIdent *ast, clang::ASTContext *c);
    // no VecExpr because we always know exactly what subtype we're creating
    coords::VecVarExpr* mkVecVarExpr(const ast::VecVarExpr *ast, clang::ASTContext *c);

    coords::VecVecAddExpr* mkVecVecAddExpr(const ast::VecVecAddExpr *ast, clang::ASTContext *c, 
                                             coords::VecExpr *mem, 
                                             coords::VecExpr *arg);

    coords::VecScalarMulExpr* mkVecScalarMulExpr(const ast::VecScalarMulExpr *ast, clang::ASTContext *c,
                                             coords::ScalarExpr *flt, coords::VecExpr *vec);


    coords::ScalarScalarAddExpr* mkScalarScalarAddExpr(const ast::ScalarScalarAddExpr *ast, clang::ASTContext *c, 
                                             coords::ScalarExpr *lhs, 
                                             coords::ScalarExpr *rhs);

    coords::ScalarScalarMulExpr* mkScalarScalarMulExpr(const ast::ScalarScalarMulExpr *ast, clang::ASTContext *c, 
                                             coords::ScalarExpr *lhs, 
                                             coords::ScalarExpr *rhs);


    // KEVIN: Added for new horizontal vector paren expr module
    coords::VecParenExpr *mkVecParenExpr(ast::VecParenExpr *ast, clang::ASTContext *c,
                                                ast::VecExpr *expr);

    coords::Vector_Lit *mkVector_Lit(const ast::Vector_Lit *ast, clang::ASTContext *c,
                                                ast::ScalarValue x, ast::ScalarValue y, ast::ScalarValue z);
    coords::Vector_Var* mkVector_Var(const ast::Vector_Var *ast, clang::ASTContext *c,
                                                coords::VecVarExpr *var);
    coords::Vector_Expr* mkVector_Expr(const ast::Vector_Expr *ctor_ast, clang::ASTContext *c,
                                             ast::VecExpr *expr_ast);
    coords::Vector_Def* mkVector_Def(const ast::Vector_Def *ast, clang::ASTContext *c,
                                             coords::VecIdent *id, 
                                             coords::VecExpr *vec);

    coords::Vector_Assign* mkVector_Assign(const ast::Vector_Assign *ast, clang::ASTContext *c,
                                             coords::VecVarExpr *var, 
                                             coords::VecExpr *vec);

    coords::ScalarIdent* mkScalarIdent(const ast::ScalarIdent *ast, clang::ASTContext *c);
    // no VecExpr because we always know exactly what subtype we're creating
    coords::ScalarVarExpr* mkScalarVarExpr(const ast::ScalarVarExpr *ast, clang::ASTContext *c);

    // KEVIN: Added for new horizontal vector paren expr module
    coords::ScalarParenExpr *mkScalarParenExpr(ast::ScalarParenExpr *ast, clang::ASTContext *c,
                                                ast::ScalarExpr *expr);

    coords::Scalar_Lit *mkScalar_Lit(const ast::Scalar_Lit *ast, clang::ASTContext *c,
                                                ast::ScalarValue scalar);
    coords::Scalar_Var* mkScalar_Var(const ast::Scalar_Var *ast, clang::ASTContext *c,
                                                coords::ScalarVarExpr *var);
    coords::Scalar_Expr* mkScalar_Expr(const ast::Scalar_Expr *ctor_ast, clang::ASTContext *c,
                                             ast::ScalarExpr *expr_ast);
    coords::Scalar_Def* mkScalar_Def(const ast::Scalar_Def *ast, clang::ASTContext *c,
                                             coords::ScalarIdent *id, 
                                             coords::ScalarExpr *flt);
    
    coords::Scalar_Assign* mkScalar_Assign(const ast::Scalar_Assign *ast, clang::ASTContext *c,
                                             coords::ScalarVarExpr *var, 
                                             coords::ScalarExpr *flt);

    coords::TransformIdent *mkTransformIdent(const ast::TransformIdent *ast, clang::ASTContext *c);
    coords::TransformVarExpr *mkTransformVarExpr(const ast::TransformVarExpr *ast, clang::ASTContext *c);
    coords::TransformParenExpr *mkTransformParenExpr(const ast::TransformParenExpr *ast, ast::TransformExpr *expr, clang::ASTContext *c);
    coords::TransformTransformComposeExpr *mkTransformTransformComposeExpr(ast::TransformExpr outer, ast::TransformExpr inner, clang::ASTContext *c);
    coords::TransformVecApplyExpr *mkTransformVecApplyExpr(ast::TransformExpr *texpr, ast::VecExpr vexpr, clang::ASTContext *c);
    coords::Transform_Lit *mkTransform_Lit(const ast::Transform_Lit *ast, ast::TransformMatrixArgExpr arg, clang::ASTContext *c);
    coords::Transform_Var *mkTransform_Var(const ast::Transform_Var *ast, const ast::TransformVarExpr *var, clang::ASTContext *c);
    coords::Transform_Expr *mkTransform_Expr(const ast::Transform_Expr *ast, ast::TransformExpr *expr, clang::ASTContext *c);
    coords::Transform_Def *mkTransform_Def(const ast::Transform_Def *ast, clang::ASTContext *c, coords::TransformIdent *id, coords::TransformExpr tfm);
    coords::Transform_Assign *mkTransform_Assign(const ast::Transform_Assign *ast, clang::ASTContext *c, coords::TransformVarExpr *var, coords::TransformExpr *);



    // TODO -- Have these routines return more specific subclass objects
    coords::Coords *getStmtCoords(const clang::Stmt *s) {
        return stmt_coords->find(s)->second;
    }

    coords::Coords *getDeclCoords(const clang::Decl *d) {
        return decl_coords->find(d)->second;
    }

    /*
    !!!! I NEED THESE BADLY. MOVING TO PUBLIC !!!!
    */
    std::unordered_map<const clang::Stmt *, coords::Coords *> *stmt_coords;
    std::unordered_map<const clang::Decl *, coords::Coords *> *decl_coords;
    std::unordered_map<coords::Coords *,const clang::Stmt *> *coords_stmt;
    std::unordered_map<coords::Coords *,const clang::Decl *> *coords_decl;

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
    
};

} // namespace

#endif