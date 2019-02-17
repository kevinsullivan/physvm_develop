#ifndef ASTTOCOORDS_H
#define ASTTOCOORDS_H

#include "AST.h"
#include "clang/AST/AST.h"
#include "Coords.h"

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
    coords::VecIdent *mkVecIdent(const ast::VecIdent *ast);
    //coords::VecLitExpr *mkVecLitExpr(const ast::VecLitExpr *ast);
    coords::VecVarExpr *mkVecVarExpr(const ast::VecVarExpr *ast);
    coords::VecVecAddExpr *mkVecVecAddExpr(const ast::VecVecAddExpr *ast);
    coords::Vector_Lit *mkVector_Lit(const ast::Vector_Lit *ast);
    coords::Vector_Var *mkVector_Var(const ast::Vector_Var *ast);
    coords::Vector_Expr *mkVector_Expr(const ast::Vector_Expr *ast);

private:
    void overrideStmt(const clang::Stmt *s, coords::Coords *c);
    void overrideDecl(const clang::Decl *d, coords::Coords *c);
    
    std::unordered_map<const clang::Stmt *, coords::Coords *> stmt_coords;
    std::unordered_map<const clang::Decl *, coords::Coords *> decl_coords;
};

} // namespace

#endif