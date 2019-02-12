#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"

namespace ast {

using Ident = const clang::VarDecl;
using Stmt  = const clang::DeclStmt;

} // namespace