#ifndef AST_H
#define AST_H

#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"

namespace ast {
// Scalar
using Scalar = float;

// Ident
using VecIdent = const clang::VarDecl;

// Expr
using VecExpr = const clang::Expr;
// TODO: this next one is wrong, just use Vector_Lit
using VecLitExpr = const clang::CXXConstructExpr;
using VecVarExpr = const clang::DeclRefExpr;
using VecVecAddExpr = const clang::CXXMemberCallExpr;

// Value
using Vector = const clang::CXXConstructExpr;
using Vector_Lit = const clang::CXXConstructExpr;
using Vector_Var = const clang::CXXConstructExpr;
using Vector_Expr = const clang::CXXConstructExpr; // A Clang Stmt!

// Def
using Vector_Def  = const clang::DeclStmt;
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
Vector_Def          Vector_Def              Vector_Def          mkVector_Def            CXXConstructExpr    VectorDeclStmtHandler, handleCXXDeclStmt (rec)     

                                                                                            CXXMemberCallExprArg0Matcher
                                                                                            handle_arg0_of_add_call (recurse)
                                                                                            CXXMemberCallExprMemberExprMatcher (paren or)
                                                                                            handle_member_expr_of_add_call (Expr*)
                                                                                            CXXConstructExprMatcher (|lit | add)

I'm afraid Vector and VecExpr are going to have the same address. There's an invariant that has to hold for search in the maps to work. What exactly is it?
*/

/*
clang::Expr inherits from clang::ValueStmt inherits from clang::Stmt. 

Inheriting from clang::Expr are
  - clang::CXXConstructExpr                 -- constructor call ((member expr + func) + args)
  - clang::DeclRefExpr                      -- reference to variable decl (VarDecl)
  - CXXMemberCallExpr, via CallExpr         --
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
Vector_Def              Vector_Def
Vector              Vector
*/

/*
Interpretation
--------------
mkVecIdent          ast::VecIdent
mkVector_Def        ast::Vector_Def, dom::it, dom::expr
mkVecAddExpr        ast::AddExpr, ast::AddExpr, dom::Expr
mkVecExpr           ast::VecExpr
mkVector            ast::VecLitExpr
mkVector            CXXXConstructExpr
*/
