#include <iostream>
#include <string>

#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"


#include "Interpretation.h"


/*
Hack to get g3log working. Should be in std in c++14 and later libraries.
*/
namespace std
{
    template<typename T, typename... Args>
    std::unique_ptr<T> make_unique(Args&&... args)
    {
        return std::unique_ptr<T>(new T(std::forward<Args>(args)...));
    }
}

#include <memory>
#include <g3log/g3log.hpp>
#include <g3log/logworker.hpp>

using namespace std;
using namespace llvm;
using namespace clang;
using namespace clang::ast_matchers;
using namespace clang::driver;
using namespace clang::tooling;


/*
Architectural decision: This component should deal in AST nodes only,
and call interpretation module to handle all other work.
*/

/**************************************************
Fundamental data structure populated by this tool
***************************************************/

interp::Interpretation interp_;

// TODO: Decide whether we should pass context to interpretation.
// Answer is probably yes. Not currently being done.

/*****************************
 * CXXConstructExpr (LITERALS) 
 *****************************/

// In Clang, a vector literal is a ctor applied to numerical args.
// There is no subordinate expression as there is when the value
// is given by an expression.
//
class HandlerForCXXConstructLitExpr : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    LOG(DEBUG) <<"main::HandlerForCXXConstructLitExpr::run. Start.\n";
    //ASTContext *context = Result.Context;
    const clang::CXXConstructExpr *lit_ast = 
      Result.Nodes.getNodeAs<clang::CXXConstructExpr>("VectorLitExpr");
    interp_.mkVector_Lit(lit_ast/*, context*/);
    LOG(DEBUG) <<"main::HandlerForCXXConstructLitExpr::run. Done.\n";
  }
};

/*******************************
 * Handle Member Call Expression
 *******************************/

//Forward-reference handlers for member (left) and argument (expressions) of add application
void handle_member_expr_of_add_call(const clang::Expr *left, ASTContext &context, SourceManager &sm);
void handle_arg0_of_add_call(const clang::Expr *right, ASTContext &context, SourceManager &sm);

/*
*/
void /*const domain::VecExpr * */handleMemberCallExpr(const CXXMemberCallExpr *ast, ASTContext *context, SourceManager &sm)
{
  LOG(DEBUG) <<"main::handleMemberCallExpr: Start, recurse on mem and arg\n";
  const clang::Expr *mem_ast = ast->getImplicitObjectArgument();
  const clang::Expr *arg_ast = ast->getArg(0);
  if (!mem_ast || !arg_ast) {
    LOG(FATAL) <<"main::handleMemberCallExpr. Null pointer error.\n";
    return;
  }
  handle_member_expr_of_add_call(mem_ast, *context, sm);
  handle_arg0_of_add_call(arg_ast, *context, sm);
  interp_.mkVecVecAddExpr(ast, mem_ast, arg_ast);
  LOG(DEBUG) <<"main::handleMemberCallExpr: Done.\n";
}

/*
TODO: CONSIDER inlining this code?
*/
class HandlerForCXXMemberCallExprRight_DeclRefExpr : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    const auto *declRefExpr_ast = Result.Nodes.getNodeAs<clang::DeclRefExpr>("DeclRefExpr");
    LOG(DEBUG) <<"main::HandlerForCXXMemberCallExprRight_DeclRefExpr: Start. DeclRefExpr = " << std::hex << declRefExpr_ast << "\n";
    interp_.mkVecVarExpr(declRefExpr_ast /*, context? */);
    LOG(DEBUG) <<"main::HandlerForCXXMemberCallExprRight_DeclRefExpr: Done.\n";
  }
};

//CXXMemberCallExpr := CXXMemberCallExprLeft + CXXMemberCallExprRight
class HandlerForCXXAddMemberCall : public MatchFinder::MatchCallback
{
public:
  //  Get left and right children of add expression and handle them by calls to other handlers
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    ASTContext *context = Result.Context;
    SourceManager &sm = context->getSourceManager();
    const CXXMemberCallExpr *memcall = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("MemberCallExpr");
    if (memcall == NULL)
    {
      LOG(FATAL) <<"main::HandlerForCXXAddMemberCall::run: null memcall\n";
      return;
    }
    handleMemberCallExpr(memcall, context, sm);
  }
};

/*
A Vector object constructed from a member expression
Precondition: Given match of type CXXConstructAddExpr
Postcondition: underlying add expression intepreted
Strategy:
  - Extract member expression on left, value expression on right
  - Recursively handle to get both of them into the system
  - Finally add node at this level to the system
*/
class HandlerForCXXConstructAddExpr : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    ASTContext *context = Result.Context;
    SourceManager &sm = context->getSourceManager();
    const CXXConstructExpr *ctor_ast = 
      Result.Nodes.getNodeAs<clang::CXXConstructExpr>("VectorConstructAddExpr");
    if (ctor_ast == NULL)
    {
      LOG(FATAL) <<"Error in HandlerForCXXConstructAddExpr::run. No constructor pointer\n";
      return;
    }
    LOG(DEBUG) <<"main::HandlerForCXXConstructAddExpr: START. CXXConstructExpr is:\n";

    const CXXMemberCallExpr *vec_vec_add_member_call_ast =
        Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("MemberCallExpr");
    if (vec_vec_add_member_call_ast == NULL)
    {
      LOG(FATAL) <<"Error in HandlerForCXXConstructAddExpr::run. No add expression pointer\n";
      return;
    }
    handleMemberCallExpr(vec_vec_add_member_call_ast, context, sm);
    LOG(DEBUG) <<"main::HandlerForCXXConstructAddExpr: Done.\n";
    interp_.mkVector_Expr(ctor_ast, vec_vec_add_member_call_ast /*, context*/);
  }
};

/*
handle_arg0_of_add_call:
match mem call right expr with
  | decl ref expr ==> decl_ref_expr_handler_
  | cxx member call expr ==> addHandler_
*/
class CXXMemberCallExprArg0Matcher
{
public:
  CXXMemberCallExprArg0Matcher()
  {
    // case: arg0 is a declaration reference expression
    // action: invoke dre_handler_::run as a match finder action
    const StatementMatcher DeclRefExprPattern = declRefExpr().bind("DeclRefExpr");
    CXXMemberCallExprArg0Matcher_.addMatcher(DeclRefExprPattern, &dre_handler_);

    // case: arg0 is a cxx member call expression
    // action: invoke addHandler_::run as a match finder action
    const StatementMatcher CXXMemberCallExprPattern = cxxMemberCallExpr().bind("MemberCallExpr");
    CXXMemberCallExprArg0Matcher_.addMatcher(CXXMemberCallExprPattern, &mce_handler_);
  }

  void match(const clang::Expr &call_rhs, ASTContext &context)
  {
    LOG(DEBUG) <<"CXXMemberCallExprArg0Matcher::match start\n";
    CXXMemberCallExprArg0Matcher_.match(call_rhs, context);
    LOG(DEBUG) <<"CXXMemberCallExprArg0Matcher::match finish\n";
  }

private:
  MatchFinder CXXMemberCallExprArg0Matcher_;
  HandlerForCXXMemberCallExprRight_DeclRefExpr dre_handler_;
  HandlerForCXXAddMemberCall mce_handler_;
};


// Handle the single argument to an add application 
//
void handle_arg0_of_add_call(const clang::Expr *arg, ASTContext &context, SourceManager &sm)
{
  LOG(DEBUG) <<"domain::VecExpr *handle_arg0_of_add_call. START matcher for AST node:\n";
  CXXMemberCallExprArg0Matcher call_right_arg0_matcher;
  call_right_arg0_matcher.match(*arg, context);
  LOG(DEBUG) <<"domain::VecExpr *handle_arg0_of_add_call. Done.\n";
}

/*
handle_member_expr_of_add_call:
match mem call expr with
  | decl ref expr ==> decl_ref_expr_handler_
  | cxx member call expr ==> addHandler_
    // case 1: arg0 is a declaration reference expression
    // action: invoke dre_handler_::run as a match finder action
    // case 2: arg0 is a cxx member call expression
    // action: invoke addHandler_::run as a match finder action
*/
class CXXMemberCallExprMemberExprMatcher
{
public:
  CXXMemberCallExprMemberExprMatcher()
  {
    const StatementMatcher DeclRefExprPattern = declRefExpr().bind("DeclRefExpr");
    CXXMemberCallExprMemberExprMatcher_.addMatcher(DeclRefExprPattern, &dre_handler_);
    const StatementMatcher ParenCXXMemberCallExprPattern = parenExpr(hasDescendant(cxxMemberCallExpr().bind("MemberCallExpr")));
    const StatementMatcher CXXMemberCallExprPattern = cxxMemberCallExpr().bind("MemberCallExpr");
    CXXMemberCallExprMemberExprMatcher_.addMatcher(CXXMemberCallExprPattern, &mce_handler_);
    CXXMemberCallExprMemberExprMatcher_.addMatcher(ParenCXXMemberCallExprPattern, &mce_handler_);
  }

  void match(const clang::Expr &call_rhs, ASTContext &context)
  {
    LOG(DEBUG) <<"main::CXXMemberCallExprMemberExprMatcher. START matching. AST is:\n";
    CXXMemberCallExprMemberExprMatcher_.match(call_rhs, context);
    LOG(DEBUG) <<"main::CXXMemberCallExprMemberExprMatcher. DONE matching.\n";
  }

private:
  MatchFinder CXXMemberCallExprMemberExprMatcher_;
  HandlerForCXXMemberCallExprRight_DeclRefExpr dre_handler_;
  HandlerForCXXAddMemberCall mce_handler_;
};

/*
Precondition:
Postcondition: member call expression is "in the system".
Strategy: Pattern matching on structure of member expressions
*/
void handle_member_expr_of_add_call(const clang::Expr *memexpr, ASTContext &context, SourceManager &sm)
{
  LOG(DEBUG) <<"main::handle_member_expr_of_add_call at " << std::hex << memexpr << "\n";
  if (memexpr == NULL)
  {
    LOG(FATAL) <<"main::handle_member_expr_of_add_call: Error.Null argument\n";
  }
  LOG(DEBUG) <<"main::handle_member_expr_of_add_call ast is (dump)\n";
  /*
      Match on structure of member expression.
    | vardeclref     :=
    | membercallexpr :=
  */
  CXXMemberCallExprMemberExprMatcher call_expr_mem_expr_matcher;
  call_expr_mem_expr_matcher.match(*memexpr, context);
  LOG(DEBUG) <<"main::handle_member_expr_of_add_call. Done. \n";
 }


/*
Implements pattern matching and dispatch on CXXConstructExpr
match CXXConstructExpr with
  | literal 3-float initializer ==> lit_handler
  | cxx member call expr (member_expr.add(arg0_expr)==> mem_call_expr_handler
*/
class CXXConstructExprMatcher
{
public:
  CXXConstructExprMatcher()
  {
    CXXConstructExprMatcher_.addMatcher(cxxConstructExpr(argumentCountIs(3)).bind("VectorLitExpr"), &litHandler_);
    CXXConstructExprMatcher_.addMatcher(
      cxxConstructExpr(hasDescendant(cxxMemberCallExpr(
        hasDescendant(memberExpr(hasDeclaration(namedDecl(
          hasName("vec_add"))))))
          .bind("MemberCallExpr")))
          .bind("VectorConstructAddExpr"), &addHandler_);
  };
  void match(const clang::CXXConstructExpr *consdecl, ASTContext *context)
  {
    CXXConstructExprMatcher_.match(*consdecl, *context);
  }

private:
  MatchFinder CXXConstructExprMatcher_;
  HandlerForCXXConstructLitExpr litHandler_;
  HandlerForCXXConstructAddExpr addHandler_;
};


/*************************
 * Handle Vector DeclStmts
 *************************/

/*
Role: Handles top-level vector declaration statements
Precondition: Receives a Vector DeclStmt object to handle
Postcondition:
  identifier node is interpreted
  expression to be bound to identifier is intepreted
  binding of identifier to expression is interpreted
*/

class VectorDeclStmtHandler : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    const clang::DeclStmt *declstmt = Result.Nodes.getNodeAs<clang::DeclStmt>("VectorDeclStatement");
    const clang::CXXConstructExpr *consdecl = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("CXXConstructExpr");
    const clang::VarDecl *vardecl = Result.Nodes.getNodeAs<clang::VarDecl>("VarDecl");
    LOG(DEBUG) <<"VectorDeclStmtHandler::run: START. AST (dump) is \n"; 
    ASTContext *context = Result.Context;
    //SourceManager &sm = context->getSourceManager();
    interp_.mkVecIdent(vardecl);
    CXXConstructExprMatcher matcher;
    matcher.match(consdecl, context);
    interp_.mkVector_Def(declstmt, vardecl, consdecl);
    LOG(DEBUG) <<"VectorDeclStmtHandler::run: Done.\n"; 
    }
};

/********************************************
 * Top-level analyzer: Match Vector DeclStmts
 ********************************************/

class MyASTConsumer : public ASTConsumer
{
public:
  MyASTConsumer()
  {
    StatementMatcher match_Vector_general_decl =
        declStmt(hasDescendant(varDecl(hasDescendant(cxxConstructExpr(hasType(asString("class Vec"))).bind("CXXConstructExpr"))).bind("VarDecl"))).bind("VectorDeclStatement");
    VectorDeclStmtMatcher.addMatcher(match_Vector_general_decl, &HandlerForVectorDeclStmt);
  }
  void HandleTranslationUnit(ASTContext &Context) override
  {
    VectorDeclStmtMatcher.matchAST(Context);
  }

private:
  MatchFinder VectorDeclStmtMatcher;
  VectorDeclStmtHandler HandlerForVectorDeclStmt;
};

/*******************************
* Main Clang Tooling entry point
********************************/

class MyFrontendAction : public ASTFrontendAction
{
public:
  MyFrontendAction() {}
  void EndSourceFileAction() override
  {
    //bool consistent = interp_.isConsistent();
    LOG(DEBUG) <<"STUB Analysis result\n";
  }
  std::unique_ptr<ASTConsumer>
  CreateASTConsumer(CompilerInstance &CI, StringRef file) override
  {
    return llvm::make_unique<MyASTConsumer>();
  }
};

/*****
* Main
******/

//INITIALIZE_EASYLOGGINGPP

/****************************
Standard Clang Tooling Set-up
*****************************/

static llvm::cl::OptionCategory MyToolCategory("Peirce options");
static cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);
static cl::extrahelp MoreHelp("No additional options available for Peirce.");

int main(int argc, const char **argv)
{
  CommonOptionsParser op(argc, argv, MyToolCategory);
  ClangTool Tool(op.getCompilations(), op.getSourcePathList());

  using namespace g3;
  std::string logFile = "Peirce.log";
  std::string logDir = ".";
  auto worker = LogWorker::createLogWorker();
  auto defaultHandler = worker->addDefaultLogger(logFile, logDir);
  g3::initializeLogging(worker.get());

  interp_.addSpace("time");
  interp_.addSpace("geom");
  
  Tool.run(newFrontendActionFactory<MyFrontendAction>().get());

  cout <<"Spaces\n";
  cout <<interp_.toString_Spaces();
  cout <<"\nIdentifiers\n";
  cout <<interp_.toString_Idents(); 
  cout <<"\nExpressions\n";
  cout <<interp_.toString_Exprs();
  cout <<"\nVectors\n";
  cout <<interp_.toString_Vectors();
  cout <<"\nDefinitions\n"; 
  cout <<interp_.toString_Defs();
}