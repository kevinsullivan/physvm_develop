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

#include "easylogging++.h"

using namespace std;
using namespace llvm;
using namespace clang;
using namespace clang::ast_matchers;
using namespace clang::driver;
using namespace clang::tooling;


/*
Architectural decision: This tool should deal in AST nodes only.
*/

/**************************************************
Fundamental data structure populated by this tool
***************************************************/

interp::Interpretation interp_;

/****************************
Standard Clang Tooling Set-up
*****************************/

static llvm::cl::OptionCategory MyToolCategory("Peirce options");
static cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);
static cl::extrahelp MoreHelp("No additional options available for Peirce.");

/*****************************
 * CXXConstructExpr (LITERALS) 
 *****************************/

// In Clang, a vector literal is a ctor applied to numerical args.
// There is no subordinate expression as there is when the value
// is given by an expression. For architectural conformity ???
//
class HandlerForCXXConstructLitExpr : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    LOG(DEBUG) <<"main::HandlerForCXXConstructLitExpr::run. Start.\n";
    ASTContext *context = Result.Context;
    const clang::CXXConstructExpr *lit_ast = 
      Result.Nodes.getNodeAs<clang::CXXConstructExpr>("VectorLitExpr");

    // NOTE: No literal expression in clang, just constructed object
    // NOTE: def will always be of identifier to constructed object
    //
    interp_.mkVector_Lit(lit_ast/*, context*/);
    LOG(DEBUG) <<"main::HandlerForCXXConstructLitExpr::run. Done.\n";
  }
};

/*******************************
 * Handle Member Call Expression
 *******************************/

//Forward-reference handlers for member (left) and argument (expressions) of add application
domain::VecExpr *handle_member_expr_of_add_call(const clang::Expr *left, ASTContext &context, SourceManager &sm);
domain::VecExpr *handle_arg0_of_add_call(const clang::Expr *right, ASTContext &context, SourceManager &sm);

/*
*/
const domain::VecExpr *handleMemberCallExpr(const CXXMemberCallExpr *ast, ASTContext *context, SourceManager &sm)
{
  LOG(DEBUG) <<"main::handleMemberCallExpr: Start, recurse on mem and arg\n";
  const clang::Expr *mem_ast = ast->getImplicitObjectArgument();
  const clang::Expr *arg_ast = ast->getArg(0);

  /*
  LOG(DEBUG) <<"Member expr AST is (dump)\n";
  mem_ast->dump();
  LOG(DEBUG) <<"Arg AST is (dump)\n";
  arg_ast->dump();
  */
 
  // TODO: Remove return values requiring knowledge of domain
  //
  const domain::VecExpr *left_br = handle_member_expr_of_add_call(mem_ast, *context, sm);
  const domain::VecExpr *right_br = handle_arg0_of_add_call(arg_ast, *context, sm);
  if (!left || !right || !left_br || !right_br) {
    LOG(DEBUG) <<"main::handleMemberCallExpr. Null pointer error.\n";
    return NULL;
  }
  //LOG(DEBUG) <<"main::handleMemberCallExpr: End\n";


  // 
  interp_.mkVecVecAddExpr(ast, mem_ast, arg_ast);
  LOG(DEBUG) <<"main::handleMemberCallExpr: Done.\n";
  return interp_.getVecExpr(ast); 
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
  
    // TODO: Should we be passing context objects with these AST nodes? Do they persist?
    //
    interp_.mkVecVarExpr(declRefExpr_ast);
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
    // TODO: Either use or omit context and sm.
    //
    ASTContext *context = Result.Context;
    SourceManager &sm = context->getSourceManager();
    const CXXMemberCallExpr *memcall = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("MemberCallExpr");
    if (memcall == NULL)
    {
      LOG(DEBUG) <<"main::HandlerForCXXAddMemberCall::run: null memcall\n";
      return;
    }
    LOG(DEBUG) <<"main::HandlerForCXXAddMemberCall. Start. Got CXXMemberCallExpr:\n";
    //memcall->dump();

    // recursive helper function
    /*const domain::VecExpr* memberCallExpr = */
    handleMemberCallExpr(memcall, context, sm);
    LOG(DEBUG) <<"main::HandlerForCXXAddMemberCall. Done.\n";
  }
};

/*
A Vector object constructed from a member expression

Precondition: Provided with match result of type CXXConstructAddExpr
Postcondition: underlying add expression in system, as child of this node, also in system
Strategy:
  - Extract member expression on left, value expression on right
  - Get both of them into the system
  - Add node at this level to the system
*/
class HandlerForCXXConstructAddExpr : public MatchFinder::MatchCallback
{
public:
  //  Get left and right children of add expression and handle them by calls to other handlers
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    ASTContext *context = Result.Context;
    SourceManager &sm = context->getSourceManager();

    // Need separate nodes for these constructors?
    //
    const CXXConstructExpr *ctor_ast = 
      Result.Nodes.getNodeAs<clang::CXXConstructExpr>("VectorConstructAddExpr");
    if (ctor_ast == NULL)
    {
      LOG(DEBUG) <<"Error in HandlerForCXXConstructAddExpr::run. No constructor declaration pointer\n";
      return;
    }
    LOG(DEBUG) <<"main::HandlerForCXXConstructAddExpr: START. CXXConstructExpr is:\n";
    //ctor_ast->dump();

    const CXXMemberCallExpr *vec_vec_add_member_call_ast =
        Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("MemberCallExpr");
    if (vec_vec_add_member_call_ast == NULL)
    {
      LOG(DEBUG) <<"Error in HandlerForCXXConstructAddExpr::run. No add expression pointer\n";
      LOG(DEBUG) <<"Surrounding CXXConstructExpr is "; 
      //vec_vec_add_member_call_ast->dump();
      return;
    }

    // Recursively handle member call expression
    //
    // TODO: Should not hMCE should not return value. Just trade in AST nodes.
    // const domain::VecExpr *memberCallExpr = handleMemberCallExpr(vec_vec_add_member_call_ast, context, sm);
    const domain::VecExpr *memberCallExpr = handleMemberCallExpr(vec_vec_add_member_call_ast, context, sm);

    // Probably want to fetch VecExpr just constructed and 
    // incorporate it as a chile of the overall node we're making


    //return interp_.mkVector_Expr(expr_ctor_ast, memberCallExpr->getCoords() /*, context*/);
    LOG(DEBUG) <<"main::HandlerForCXXConstructAddExpr: Done. Returning domain Vector_Expr (unnecessary)\n";

    // TODO: Omit return value here. Simplify.
    return interp_.mkVector_Expr(ctor_ast, vec_vec_add_member_call_ast /*, context*/);
  }
};

/***** Handle Right Expr of expr.add(expr) Call Expr ******/

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

/*
Handle the single argument to an add application 
*/
domain::VecExpr *handle_arg0_of_add_call(const clang::Expr *arg, ASTContext &context, SourceManager &sm)
{
  LOG(DEBUG) <<"domain::VecExpr *handle_arg0_of_add_call. START matcher for AST node:\n";
  //arg->dump();

  CXXMemberCallExprArg0Matcher call_right_arg0_matcher;
  call_right_arg0_matcher.match(*arg, context);
  // postcondition, arg is now "in the system" as a domain expression
  // find and return resulting domain expression
  //
  // TODO: Clear this up, move next line into getVecExpr, no need to return value
  //
  LOG(DEBUG) <<"domain::VecExpr *handle_arg0_of_add_call. Done.\n";
  return interp_.getVecExpr(arg);
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
    
    //const StatementMatcher DeclRefExprPattern = memberExpr(parenExpr(declRefExpr().bind("LeftDeclRefExpr")));

    const StatementMatcher ParenCXXMemberCallExprPattern = parenExpr(hasDescendant(cxxMemberCallExpr().bind("MemberCallExpr")));

    const StatementMatcher CXXMemberCallExprPattern = cxxMemberCallExpr().bind("MemberCallExpr");

    CXXMemberCallExprMemberExprMatcher_.addMatcher(CXXMemberCallExprPattern, &mce_handler_);

    CXXMemberCallExprMemberExprMatcher_.addMatcher(ParenCXXMemberCallExprPattern, &mce_handler_);
  }

  void match(const clang::Expr &call_rhs, ASTContext &context)
  {
    // NO MATCH HAPPENING HERE!
    LOG(DEBUG) <<"main::CXXMemberCallExprMemberExprMatcher. START matching. AST is:\n";
    //call_rhs.dump();
    CXXMemberCallExprMemberExprMatcher_.match(call_rhs, context);
    LOG(DEBUG) <<"main::CXXMemberCallExprMemberExprMatcher. DONE matching.\n";
  // Postcondtion: member expression in call now "in system" as dom Expr
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
domain::VecExpr *handle_member_expr_of_add_call(const clang::Expr *memexpr, ASTContext &context, SourceManager &sm)
{
  LOG(DEBUG) <<"main::handle_member_expr_of_add_call at " << std::hex << memexpr << "\n";
  if (memexpr == NULL)
  {
    LOG(DEBUG) <<"main::handle_member_expr_of_add_call: Error.Null argument\n";
  }
  LOG(DEBUG) <<"main::handle_member_expr_of_add_call ast is (dump)\n";
  //memexpr->dump();


  // PROBLEM ZONE
  /*
      Match on structure of member expression.
    | vardeclref     :=
    | membercallexpr :=
  */
  LOG(DEBUG) <<"domain::VecExpr *handle_member_expr_of_add_call: match memexpr START.\n"; CXXMemberCallExprMemberExprMatcher call_expr_mem_expr_matcher;
  call_expr_mem_expr_matcher.match(*memexpr, context);
  LOG(DEBUG) <<"domain::VecExpr *handle_member_expr_of_add_call: match memexpr DONE.\n"; 
  //
  // Postcondition: member expression is "in the system" as dom expr
  // keyed by memexpr (by an AST wrapper around memexpr).
  // Test postcondition.

  domain::VecExpr *expr = interp_.getVecExpr(memexpr);
  LOG(DEBUG) <<"domain::VecExpr *handle_member_expr_of_add_call. Done. \n";
  return expr; 
 }


/*
Implements pattern matching and dispatch on CXXConstructExpr

match CXXConstructExpr with
  | literal 3-float initializer ==> lit_handler
  | cxx member call expr (member_expr.add(arg0_expr)==> mem_call_expr_handler
*/
class CXXConstructExprMatcher // (Constructor = Lit | Add left right )
{
public:
  CXXConstructExprMatcher()
  {
    CXXConstructExprMatcher_.addMatcher(cxxConstructExpr(argumentCountIs(3)).bind("VectorLitExpr"), &litHandler_);
    // KEVBOB
    CXXConstructExprMatcher_.addMatcher(
      cxxConstructExpr(hasDescendant(cxxMemberCallExpr(
        hasDescendant(memberExpr(hasDeclaration(namedDecl(
          hasName("vec_add"))))))
          .bind("MemberCallExpr")))
          .bind("VectorConstructAddExpr"), &addHandler_);
  };
  void match(const clang::CXXConstructExpr *consdecl, ASTContext *context)
  {
    LOG(DEBUG) <<"START: Pattern Matching on CXXConstructExpr (Lit | Add): Start\n";
    CXXConstructExprMatcher_.match(*consdecl, *context);
    LOG(DEBUG) <<"DONE: Pattern Matching on CXXConstructExpr (Lit | Add): End\n";
    //
    // Postcondition: identifier and lit or add expression binding is in system
    // Nothing else to do, client will pick up resulting expression via interp
  }

private:
  MatchFinder CXXConstructExprMatcher_;
  HandlerForCXXConstructLitExpr litHandler_;
  HandlerForCXXConstructAddExpr addHandler_;
};

//--------------------

//const domain::VecExpr* handleMemberCall

//--------------------

/*
Precondition: consdecl of type CXXConstructExpr* is a pointer to an 
expression, the value of which is being assigned to a variable in a 
declaration statement. 

Explanation: By the time control reaches this code, we are assured 
the argument is an AST node for a Vector-valued expression that is
going to be used to initialize the value of a variable. The purpose 
of this code is to make sure that this C++ expression is "lifted" to
a corresponding expression in the domain, and that the
interpretation links this code/AST-node to that domain object.

Postcondition: the return value of this function is pointer to a new 
object of type domain::VecExpr; that object is in the domain; it might
itself represent a complex expression tree; it links back to consdecl;
and the interpretation is updated to like consdecl to the new domain
object. This function works recursively to make sure that all of the
work of handling the top-level CXXConstructExpr is finished by the 
time this function returns.

Explanation: the way in which this consdecl is turned into a domain 
object depends on the specific form of the expression being handled.
The cases to be handled include literal and add expressions.
- Vec v1(0.0,0.0,0.0) is a literal expression
- (v1.add(v2)).(v3.add(v4)) is an add expression (recursive)

domain::VecExpr *handleCXXConstructExpr(const clang::CXXConstructExpr *consdecl, ASTContext *context, SourceManager &sm)
{
  //LOG(DEBUG) <<"handleCXXConstructExpr: Start handleCXXConstructExpr\n";
  //LOG(DEBUG) <<"Pattern matching Vector CXXConstructExpr.\n";
  CXXConstructExprMatcher matcher;
  matcher.match(consdecl, context);
  // postcondition: consdecl now has an interpretation
  // How do we get BI to return to user? Look it up
  // domain::VecExpr* bi = interp->getExpr(consdecl);
  // TO DO: Architectural change means we need to wrap consdecl to map it

  const Expr *ast = new Expr(consdecl);   // TODO -- BETTER TYPE!
  domain::VecExpr *be = interp->getVecExpr(*ast);
  //LOG(DEBUG) <<"handleCXXConstructExpr: Returning Expr at " << std::hex << be << "\n";
  return be;
}
*/

const domain::VecExpr *handleCXXDeclStmt(const clang::CXXConstructExpr *consdecl, ASTContext *context, SourceManager &sm)
{
  LOG(DEBUG) <<"domain::handleCXXDeclStmt: START. Matching.\n";
  CXXConstructExprMatcher matcher;
  matcher.match(consdecl, context);
  //
  // postcondition: consdecl now "in the system" (has interpretation)
  // Fetch and return result
  //
  const domain::VecExpr *expr = interp_.getVecExpr(consdecl);
  LOG(DEBUG) <<"domain::handleCXXDeclStmt: DONE. domain::VecExpr at " 
    << std::hex << expr << "\n";
  return expr;
}

/*************************
 * Handle Vector DeclStmts
 *************************/

/*
Role: Handles top-level vector declaration statements

Precondition: Receives a Vector DeclStmt object to handle
Postcondition:
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
    //declstmt->dump();

    ASTContext *context = Result.Context;
    SourceManager &sm = context->getSourceManager();

    // IDENTIFIER -- should call handle identifier (TODO:)
    //
    interp_.mkVecIdent(vardecl);
    
    // CONSTRUCTOR (VecLitExpr | Add)
    //
    LOG(DEBUG) <<"VectorDeclStmtHandler: start matching on consdecl\n";
    CXXConstructExprMatcher matcher;
    matcher.match(consdecl, context);
    LOG(DEBUG) <<"VectorDeclStmtHandler: done matching on consdecl\n";
    //
    // Postcondition: domain vector expression now in system
    // fetch result. Checking occurs in getVecExpr.
  
    // add domain::Vector_Def for variable declaration statement in code
    //
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

INITIALIZE_EASYLOGGINGPP

int main(int argc, const char **argv)
{
  CommonOptionsParser op(argc, argv, MyToolCategory);
  ClangTool Tool(op.getCompilations(), op.getSourcePathList());

  START_EASYLOGGINGPP(argc, argv);

  // easylogging configuration file is in /usr/local/easylogging.conf
  // change it there, or select a different file for yourself, below.
  //
  el::Loggers::configureFromGlobal("/usr/local/easylogging.conf");


  // Initialize interpretation with spaces implicit in code to be analyzed
  //
  interp_.addSpace("time");
  interp_.addSpace("geom");
  
  Tool.run(newFrontendActionFactory<MyFrontendAction>().get());

  // See what we got
  //
  cout <<"Spaces\n";
  cout <<interp_.toString_Spaces();
  cout <<"Identifiers\n";
  cout <<interp_.toString_Idents(); 
  cout <<"Expressions\n";
  cout <<interp_.toString_Exprs();
  cout <<"Vectors\n";
  cout <<interp_.toString_Vectors();
  cout <<"Definitions\n"; 
  cout <<interp_.toString_Defs();
}