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
Coords
------
VectorExpr (common base class)
VectorLit 
VecIdent 
VarDeclRef 
VectorAddExpr 
AddConstruct : VectorExpr (no hasher, unused?)
Vector
Binding
*/

/*
Domain
------
Space
Identifier
Expr
VecLitExpr
VecVarExpr
VecAddExpr
Binding
Vector
Domain
*/