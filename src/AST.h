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
