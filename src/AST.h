#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"

namespace ast {

// TODO: Remove const if we want to modify AST
// TODO: Prefix with Vec
//
using Vector = const clang::CXXConstructExpr;
using VectorLiteral = const clang::CXXConstructExpr;
using Ident = const clang::VarDecl;
using Stmt  = const clang::DeclStmt;
using Expr = const clang::Expr;
using Binding = const clang::VarDecl; 
using AddExpr = const clang::CXXMemberCallExpr;
using Var = const clang::DeclRefExpr;
using WHAT = const clang::DeclStmt; // for DeclStmt

} // namespace

