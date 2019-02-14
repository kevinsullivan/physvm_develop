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
using VecDef  = const clang::DeclStmt;
using VecIdent = const clang::VarDecl;
using VecCtor = const clang::CXXConstructExpr;
using VecExpr = const clang::Expr;
using VecLitExpr = const clang::CXXConstructExpr;
using VecVecAddExpr = const clang::CXXMemberCallExpr;
using VecVarExpr = const clang::DeclRefExpr;
} // namespace

#endif

/*
Domain                  Coords              AST
------                  ------              ---
Space
VecExpr                 VecExpr (super)     tagged union type
VecLitExpr              VecLitExpr          ast::VecLitExpr
VecIdent                VecIdent            ast::VecIdent
VecVarExpr              VecVarExpr          ast::VecVarExpr          
VecVecAddExpr           VecVecAddExpr       ast::VecVecAddExpr,coords:VecExpr
Vector                  AddConstruct        (unused? nope, see Domain Vector)
                        Vector              clang::CXXConstructExpr 
Binding                 Binding             ast::VecDef
*/

/*
Domain              Coords
------              ------
Space
VecIdent          VecIdent
Expr                VecExpr
VecLitExpr          VecLitExpr
VecVarExpr          VecVarExpr
VecVecAddExpr          VecVecVecAddExpr
Binding             Binding
Vector              AddConstruct
*/

/*
Interpretation
--------------
mkVecIdent          ast::VecIdent
mkVecBinding        ast::VecDef, dom::it, dom::expr
mkVecAddExpr        ast::AddExpr, ast::AddExpr, dom::Expr
mkVecExpr           ast::VecExpr
mkVector            ast::VecLitExpr
mkVector            CXXXConstructExpr
*/
