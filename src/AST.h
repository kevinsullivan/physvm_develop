#ifndef AST_H
#define AST_H

#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"

namespace ast {

// TODO: Remove const if we want to modify AST
// TODO: Prefix with Vec
//
// What is the invariant needed for lookups to work?
//
using VecDef  = const clang::DeclStmt;
using Vector = const clang::CXXConstructExpr;
using VecIdent = const clang::VarDecl;
using VecExpr = const clang::Expr;
using VecLitExpr = const clang::CXXConstructExpr;
using VecVarExpr = const clang::DeclRefExpr;
using VecVecAddExpr = const clang::CXXMemberCallExpr;
} // namespace

#endif

/*
Domain          Coords              AST             Interp
------          ------              ---             -------
Space
VecExpr         VecExpr (super)     union           mkVecExpr
VecLitExpr      VecLitExpr          VecLitExpr      (uses mkVector)
VecIdent        VecIdent            VecIdent        mkVecIdent
VecVarExpr      VecVarExpr          VecVarExpr      mkVecVarExpr   
VecVecAddExpr   VecVecAddExpr       VecVecAddExpr   mkVecVecAddExpr
Vector          Vector              Vector          mkVector
VecDef          VecDef              VecDef          mkVecDef

I'm afraid Vector and VecExpr are going to have the same address. There's an invariant that has to hold for search in the maps to work. What exactly is it?
*/

/*
Domain              Coords
------              ------
Space
VecIdent            VecIdent
Expr                VecExpr
VecLitExpr          VecLitExpr
VecVarExpr          VecVarExpr
VecVecAddExpr       VecVecVecAddExpr
VecDef             VecDef
Vector              Vector
*/

/*
Interpretation
--------------
mkVecIdent          ast::VecIdent
mkVecDef        ast::VecDef, dom::it, dom::expr
mkVecAddExpr        ast::AddExpr, ast::AddExpr, dom::Expr
mkVecExpr           ast::VecExpr
mkVector            ast::VecLitExpr
mkVector            CXXXConstructExpr
*/
