
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
using MAIN_STMT = const clang::FunctionDecl;
using FUNCTION_STMT = const clang::FunctionDecl;
using STMT = const clang::Stmt;
using COMPOUND_STMT = const clang::Stmt;
using IFCOND = const clang::Stmt;
using IFTHEN_EXPR_STMT = const clang::Stmt;
using IFTHENELSEIF_EXPR_STMT_IFCOND = const clang::Stmt;
using IFTHENELSE_EXPR_STMT_STMT = const clang::Stmt;
using EXPR = const clang::Stmt;
using REAL3_EXPR = const clang::Stmt;
using REAL1_EXPR = const clang::Stmt;
using REALMATRIX_EXPR = const clang::Stmt;
using REAL4_EXPR = const clang::Stmt;
using ASSIGNMENT = const clang::Stmt;
using ASSIGN_REAL1_VAR_REAL1_EXPR = const clang::Stmt;
using ASSIGN_REAL3_VAR_REAL3_EXPR = const clang::Stmt;
using ASSIGN_REAL4_VAR_REAL4_EXPR = const clang::Stmt;
using ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR = const clang::Stmt;
using DECLARE = const clang::Stmt;
using DECL_REAL1_VAR_REAL1_EXPR = const clang::Stmt;
using DECL_REAL3_VAR_REAL3_EXPR = const clang::Stmt;
using DECL_REAL4_VAR_REAL4_EXPR = const clang::Stmt;
using DECL_REALMATRIX_VAR_REALMATRIX_EXPR = const clang::Stmt;
using DECL_REAL1_VAR = const clang::Stmt;
using DECL_REAL3_VAR = const clang::Stmt;
using DECL_REAL4_VAR = const clang::Stmt;
using DECL_REALMATRIX_VAR = const clang::Stmt;
using REAL1_EXPR = const clang::Stmt;
using PAREN_REAL1_EXPR = const clang::Stmt;
using INV_REAL1_EXPR = const clang::Stmt;
using NEG_REAL1_EXPR = const clang::Stmt;
using ADD_REAL1_EXPR_REAL1_EXPR = const clang::Stmt;
using SUB_REAL1_EXPR_REAL1_EXPR = const clang::Stmt;
using MUL_REAL1_EXPR_REAL1_EXPR = const clang::Stmt;
using DIV_REAL1_EXPR_REAL1_EXPR = const clang::Stmt;
using REF_REAL1_VAR = const clang::Stmt;
using REAL3_EXPR = const clang::Stmt;
using PAREN_REAL3_EXPR = const clang::Stmt;
using ADD_REAL3_EXPR_REAL3_EXPR = const clang::Stmt;
using SUB_REAL3_EXPR_REAL3_EXPR = const clang::Stmt;
using INV_REAL3_EXPR = const clang::Stmt;
using NEG_REAL3_EXPR = const clang::Stmt;
using MUL_REAL3_EXPR_REAL1_EXPR = const clang::Stmt;
using MUL_REALMATRIX_EXPR_REAL3_EXPR = const clang::Stmt;
using DIV_REAL3_EXPR_REAL1_EXPR = const clang::Stmt;
using REF_REAL3_VAR = const clang::Stmt;
using REAL4_EXPR = const clang::Stmt;
using PAREN_REAL4_EXPR = const clang::Stmt;
using ADD_REAL4_EXPR_REAL4_EXPR = const clang::Stmt;
using MUL_REAL4_EXPR_REAL1_EXPR = const clang::Stmt;
using REF_REAL4_VAR = const clang::Stmt;
using REALMATRIX_EXPR = const clang::Stmt;
using PAREN_REALMATRIX_EXPR = const clang::Stmt;
using MUL_REALMATRIX_EXPR_REALMATRIX_EXPR = const clang::Stmt;
using REF_EXPR_REALMATRIX_VAR = const clang::Stmt;
using REAL1_VAR_IDENT = const clang::VarDecl;
using REAL3_VAR_IDENT = const clang::VarDecl;
using REAL4_VAR_IDENT = const clang::VarDecl;
using REALMATRIX_VAR_IDENT = const clang::VarDecl;
using REAL1_LITERAL = const clang::Stmt;
using REAL1_LITERAL1 = const clang::Stmt;
using REAL3_LITERAL = const clang::Stmt;
using REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR = const clang::Stmt;
using REAL3_LITERAL3 = const clang::Stmt;
using REAL4_LITERAL = const clang::Stmt;
using REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR = const clang::Stmt;
using REAL4_LITERAL4 = const clang::Stmt;
using REALMATRIX_LITERAL = const clang::Stmt;
using REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR = const clang::Stmt;
using REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR = const clang::Stmt;
using REALMATRIX_LITERAL9 = const clang::Stmt;

} // namespace

#endif


