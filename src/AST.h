#ifndef AST_H
#define AST_H

#include "clang/AST/AST.h"
//#include "clang/AST/ASTConsumer.h"
//#include "clang/AST/Expr.h"
//#include "clang/AST/Stmt.h"


namespace ast {
// Scalar
using Scalar = float;

// Wrapper
using ExprWithCleanupsWrapper = const clang::ExprWithCleanups;
using ImplicitCastExprWrapper = const clang::ImplicitCastExpr;

// Ident
using VecIdent = const clang::VarDecl;
using FloatIdent = const clang::VarDecl;

// Expr
using VecExpr = const clang::Expr;
using VecLitExpr = const clang::CXXConstructExpr;
using VecVarExpr = const clang::DeclRefExpr;
using VecVecAddExpr = const clang::CXXMemberCallExpr;


using FloatExpr = const clang::Expr;
using FloatLitExpr = const clang::CXXConstructExpr;
using FloatVarExpr = const clang::DeclRefExpr;

using VecScalarMulExpr = const clang::CXXMemberCallExpr;

// KEVIN: Add for VecParenExpr module
using VecParenExpr = const clang::ParenExpr;

using FloatParenExpr = const clang::ParenExpr;

// Value
using Vector = const clang::CXXConstructExpr;
using Vector_Lit = const clang::CXXConstructExpr;
using Vector_Var = const clang::CXXConstructExpr;
using Vector_Expr = const clang::CXXConstructExpr; // A Clang Stmt!

using Float = const clang::CXXConstructExpr;
using Float_Lit = const clang::CXXConstructExpr;
using Float_Var = const clang::CXXConstructExpr;
using Float_Expr = const clang::CXXConstructExpr;


// Def
using Vector_Def  = const clang::DeclStmt;

using Float_Def = const clang::DeclStmt;
} // namespace

#endif
