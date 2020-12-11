
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

} // namespace

#endif


