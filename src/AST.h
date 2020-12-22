
#ifndef AST_H
#define AST_H

#include "clang/AST/AST.h"
//#include "clang/AST/ASTConsumer.h"
//#include "clang/AST/Expr.h"
//#include "clang/AST/Stmt.h"


namespace ast{

using RealScalar = double;


using PROGRAM = const clang::TranslationUnitDecl;
using SEQ_GLOBALSTMT = const clang::TranslationUnitDecl;
using GLOBALSTMT = const clang::FunctionDecl;
using STMT = const clang::Stmt;
using COMPOUND_STMT = const clang::Stmt;
using FUNC_DECL = const clang::Stmt;
using VOID_FUNC_DECL_STMT = const clang::FunctionDecl;
using MAIN_FUNC_DECL_STMT = const clang::FunctionDecl;
using DECLARE = const clang::Stmt;
using DECL_REAL1_VAR_REAL1_EXPR = const clang::Stmt;
using DECL_REAL3_VAR_REAL3_EXPR = const clang::Stmt;
using DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR = const clang::Stmt;
using DECL_REAL1_VAR = const clang::Stmt;
using DECL_REAL3_VAR = const clang::Stmt;
using DECL_REALMATRIX4_VAR = const clang::Stmt;
using REXPR = const clang::Stmt;
using LEXPR = const clang::Stmt;
using REALMATRIX4_EXPR = const clang::Stmt;
using REF_REALMATRIX4_VAR = const clang::Stmt;
using MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR = const clang::Stmt;
using REAL3_EXPR = const clang::Stmt;
using REF_REAL3_VAR = const clang::Stmt;
using ADD_REAL3_EXPR_REAL3_EXPR = const clang::Stmt;
using LMUL_REAL1_EXPR_REAL3_EXPR = const clang::Stmt;
using RMUL_REAL3_EXPR_REAL1_EXPR = const clang::Stmt;
using TMUL_REALMATRIX4_EXPR_REAL3_EXPR = const clang::Stmt;
using REAL3_LEXPR = const clang::Stmt;
using LREF_REAL3_VAR = const clang::Stmt;
using REAL1_EXPR = const clang::Stmt;
using REF_REAL1_VAR = const clang::Stmt;
using ADD_REAL1_EXPR_REAL1_EXPR = const clang::Stmt;
using MUL_REAL1_EXPR_REAL1_EXPR = const clang::Stmt;
using REAL1_VAR_IDENT = const clang::VarDecl;
using REAL3_VAR_IDENT = const clang::VarDecl;
using REALMATRIX4_VAR_IDENT = const clang::VarDecl;
using REAL3_LITERAL = const clang::Stmt;
using REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR = const clang::Stmt;
using REAL3_EMPTY = const clang::Stmt;
using REAL1_LITERAL = const clang::Stmt;
using REAL1_LIT = const clang::Stmt;
using REALMATRIX4_LITERAL = const clang::Stmt;
using REALMATRIX4_EMPTY = const clang::Stmt;

} // namespace

#endif


