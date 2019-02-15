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
Domain          Coords              AST             Interp              Clang               Main
------          ------              ---             -------             -----               ----
Space
VecExpr         VecExpr (super)     union           mkVecExpr           
VecLitExpr      VecLitExpr          VecLitExpr      (uses mkVector)
VecIdent        VecIdent            VecIdent        mkVecIdent          CXXConstructExpr    HandlerForCXXConstructLitExpr
VecVarExpr      VecVarExpr          VecVarExpr      mkVecVarExpr        DeclRefExpr         HandlerForCXXMemberCallExprRight_DeclRefExpr
VecVecAddExpr   VecVecAddExpr       VecVecAddExpr   mkVecVecAddExpr     CXXMemberCallExpr   HandlerForCXXAddMemberCall, handleMemberCallExpr
Vector          Vector              Vector          mkVector            CXXConstructExpr    HandlerForCXXConstructAddExpr (recurse member)
VecDef          VecDef              VecDef          mkVecDef            CXXConstructExpr    VectorDeclStmtHandler, handleCXXDeclStmt (rec)     

                                                                                            CXXMemberCallExprArg0Matcher
                                                                                            handle_arg0_of_add_call (recurse)
                                                                                            CXXMemberCallExprMemberExprMatcher (paren or)
                                                                                            handle_member_expr_of_add_call (Expr*)
                                                                                            CXXConstructExprMatcher (|lit | add)

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
