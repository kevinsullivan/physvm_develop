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
    std::cerr << "main::HandlerForCXXConstructLitExpr::run. Start.\n";
    ASTContext *context = Result.Context;
    const clang::CXXConstructExpr *lit_ast = 
      Result.Nodes.getNodeAs<clang::CXXConstructExpr>("VectorLitExpr");

    // NOTE: No literal expression in clang, just constructed object
    // NOTE: def will always be of identifier to constructed object
    //
    interp_.mkVector_Lit(lit_ast/*, context*/);
    std::cerr << "main::HandlerForCXXConstructLitExpr::run. Done.\n";
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
  std::cerr << "main::handleMemberCallExpr: Start, recurse on mem and arg\n";
  const clang::Expr *mem_ast = ast->getImplicitObjectArgument();
  const clang::Expr *arg_ast = ast->getArg(0);

  /*
  std::cerr << "Member expr AST is (dump)\n";
  mem_ast->dump();
  std::cerr << "Arg AST is (dump)\n";
  arg_ast->dump();
  */
 
  // TODO: Remove return values requiring knowledge of domain
  //
  const domain::VecExpr *left_br = handle_member_expr_of_add_call(mem_ast, *context, sm);
  const domain::VecExpr *right_br = handle_arg0_of_add_call(arg_ast, *context, sm);
  if (!left || !right || !left_br || !right_br) {
    std::cerr << "main::handleMemberCallExpr. Null pointer error.\n";
    return NULL;
  }
  //std::cerr << "main::handleMemberCallExpr: End\n";


  // 
  interp_.mkVecVecAddExpr(ast, mem_ast, arg_ast);
  std::cerr << "main::handleMemberCallExpr: Done.\n";
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
    std::cerr << "main::HandlerForCXXMemberCallExprRight_DeclRefExpr: Start. DeclRefExpr = " << std::hex << declRefExpr_ast << "\n";
  
    // TODO: Should we be passing context objects with these AST nodes? Do they persist?
    //
    interp_.mkVecVarExpr(declRefExpr_ast);
    std::cerr << "main::HandlerForCXXMemberCallExprRight_DeclRefExpr: Done.\n";
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
      std::cerr << "main::HandlerForCXXAddMemberCall::run: null memcall\n";
      return;
    }
    std::cerr << "main::HandlerForCXXAddMemberCall. Start. Got CXXMemberCallExpr:\n";
    memcall->dump();

    // recursive helper function
    /*const domain::VecExpr* memberCallExpr = */
    handleMemberCallExpr(memcall, context, sm);
    std::cerr << "main::HandlerForCXXAddMemberCall. Done.\n";
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
      std::cerr << "Error in HandlerForCXXConstructAddExpr::run. No constructor declaration pointer\n";
      return;
    }
    std::cerr << "main::HandlerForCXXConstructAddExpr: START. CXXConstructExpr is:\n";
    ctor_ast->dump();

    const CXXMemberCallExpr *vec_vec_add_member_call_ast =
        Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("MemberCallExpr");
    if (vec_vec_add_member_call_ast == NULL)
    {
      std::cerr << "Error in HandlerForCXXConstructAddExpr::run. No add expression pointer\n";
      std::cerr << "Surrounding CXXConstructExpr is "; vec_vec_add_member_call_ast->dump();
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
    std::cerr << "main::HandlerForCXXConstructAddExpr: Done. Returning domain Vector_Expr (unnecessary)\n";

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
    std::cerr << "CXXMemberCallExprArg0Matcher::match start\n";
    CXXMemberCallExprArg0Matcher_.match(call_rhs, context);
    std::cerr << "CXXMemberCallExprArg0Matcher::match finish\n";
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
  std::cerr << "domain::VecExpr *handle_arg0_of_add_call. START matcher for AST node:\n";
  arg->dump();

  CXXMemberCallExprArg0Matcher call_right_arg0_matcher;
  call_right_arg0_matcher.match(*arg, context);
  // postcondition, arg is now "in the system" as a domain expression
  // find and return resulting domain expression
  //
  // TODO: Clear this up, move next line into getVecExpr, no need to return value
  //
  std::cerr << "domain::VecExpr *handle_arg0_of_add_call. Done.\n";
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
    std::cerr << "main::CXXMemberCallExprMemberExprMatcher. START matching. AST is:\n";
      call_rhs.dump();
    CXXMemberCallExprMemberExprMatcher_.match(call_rhs, context);
    std::cerr << "main::CXXMemberCallExprMemberExprMatcher. DONE matching.\n";
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
  std::cerr << "main::handle_member_expr_of_add_call at " << std::hex << memexpr << "\n";
  if (memexpr == NULL)
  {
    std::cerr << "main::handle_member_expr_of_add_call: Error.Null argument\n";
  }
  std::cerr << "main::handle_member_expr_of_add_call ast is (dump)\n";
  memexpr->dump();


  // PROBLEM ZONE
  /*
      Match on structure of member expression.
    | vardeclref     :=
    | membercallexpr :=
  */
  std::cerr << "domain::VecExpr *handle_member_expr_of_add_call: match memexpr START.\n"; CXXMemberCallExprMemberExprMatcher call_expr_mem_expr_matcher;
  call_expr_mem_expr_matcher.match(*memexpr, context);
  std::cerr << "domain::VecExpr *handle_member_expr_of_add_call: match memexpr DONE.\n"; 
  //
  // Postcondition: member expression is "in the system" as dom expr
  // keyed by memexpr (by an AST wrapper around memexpr).
  // Test postcondition.

  domain::VecExpr *expr = interp_.getVecExpr(memexpr);
  std::cerr << "domain::VecExpr *handle_member_expr_of_add_call. Done. \n";
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
    std::cerr << "START: Pattern Matching on CXXConstructExpr (Lit | Add): Start\n";
    CXXConstructExprMatcher_.match(*consdecl, *context);
    std::cerr << "DONE: Pattern Matching on CXXConstructExpr (Lit | Add): End\n";
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
  //std::cerr << "handleCXXConstructExpr: Start handleCXXConstructExpr\n";
  //std::cerr << "Pattern matching Vector CXXConstructExpr.\n";
  CXXConstructExprMatcher matcher;
  matcher.match(consdecl, context);
  // postcondition: consdecl now has an interpretation
  // How do we get BI to return to user? Look it up
  // domain::VecExpr* bi = interp->getExpr(consdecl);
  // TO DO: Architectural change means we need to wrap consdecl to map it

  const Expr *ast = new Expr(consdecl);   // TODO -- BETTER TYPE!
  domain::VecExpr *be = interp->getVecExpr(*ast);
  //std::cerr << "handleCXXConstructExpr: Returning Expr at " << std::hex << be << "\n";
  return be;
}
*/

const domain::VecExpr *handleCXXDeclStmt(const clang::CXXConstructExpr *consdecl, ASTContext *context, SourceManager &sm)
{
  std::cerr << "domain::handleCXXDeclStmt: START. Matching.\n";
  CXXConstructExprMatcher matcher;
  matcher.match(consdecl, context);
  //
  // postcondition: consdecl now "in the system" (has interpretation)
  // Fetch and return result
  //
  const domain::VecExpr *expr = interp_.getVecExpr(consdecl);
  std::cerr << "domain::handleCXXDeclStmt: DONE. domain::VecExpr at " 
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
    std::cerr << "VectorDeclStmtHandler::run: START. AST (dump) is \n"; 
    declstmt->dump();

    ASTContext *context = Result.Context;
    SourceManager &sm = context->getSourceManager();

    // IDENTIFIER -- should call handle identifier (TODO:)
    //
    interp_.mkVecIdent(vardecl);
    
    // CONSTRUCTOR (VecLitExpr | Add)
    //
    std::cerr << "VectorDeclStmtHandler: start matching on consdecl\n";
    CXXConstructExprMatcher matcher;
    matcher.match(consdecl, context);
    std::cerr << "VectorDeclStmtHandler: done matching on consdecl\n";
    //
    // Postcondition: domain vector expression now in system
    // fetch result. Checking occurs in getVecExpr.
  
    // add domain::Vector_Def for variable declaration statement in code
    //
    interp_.mkVector_Def(declstmt, vardecl, consdecl);
    std::cerr << "VectorDeclStmtHandler::run: Done.\n"; 
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
    std::cerr << "STUB Analysis result\n";
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

int main(int argc, const char **argv)
{
  CommonOptionsParser op(argc, argv, MyToolCategory);
  ClangTool Tool(op.getCompilations(), op.getSourcePathList());

  interp_.addSpace("S1");
  interp_.addSpace("S2");
  
  Tool.run(newFrontendActionFactory<MyFrontendAction>().get());

  std::cerr << " Spaces\n";
  std::cerr << interp_.toString_Spaces();
  std::cerr << "Identifiers\n";
  std::cerr << interp_.toString_Idents();
  std::cerr << "Expressions\n";
  std::cerr << interp_.toString_Exprs();
  std::cerr << "Vectors\n";
  std::cerr << interp_.toString_Vectors();
  std::cerr << "Definitions\n"; 
  std::cerr << interp_.toString_Defs();
}