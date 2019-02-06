#include <string>
#include <iostream>
#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Expr.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"

#include "CodeCoordinate.h"
#include "Interpretation.h"
#include "Oracle.h"
#include "Bridge.h"

using namespace clang;
using namespace clang::ast_matchers;
using namespace clang::driver;
using namespace clang::tooling;
using namespace std;
using namespace llvm;
using namespace bridge;

/**************************************************
Fundamental data structure constructed by this tool
***************************************************/

/*
Sharing data via global variables is a bad idea, but we'll 
do it to get a working system. These variables are initialized 
in main() and updated during the parse tree traversal, as AST
node handlers are triggered. 
*/
Oracle *oracle;
Bridge *bridge_domain;
Interpretation *interp;

/****************************
Standard Clang Tooling Set-up
*****************************/

/*
Set up a custom category for all command-line options; a help 
message with Clang's standard common command-line options; and 
a tool-specific help message.
*/
static llvm::cl::OptionCategory MyToolCategory("Peirce options");
static cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);
static cl::extrahelp MoreHelp("No additional options available for Peirce.");

/***************************
 * CXXConstructExpr HANDLERS
 ***************************/

/*
Function: Add interpretation for Vector identifier

create a bridge variable object 
add interpretation from vardecl to bridge variable object
maybe return a bool or something to indicate success or failure?
*/
bridge::Identifier* handleCXXConstructIdentifier(const VarDecl *vardecl, ASTContext *context, SourceManager &sm)
{

/*
  main.cpp:69:56: error: no matching function for call to 'Oracle::getSpaceForIdentifier(const clang::VarDecl*&)'
   Space& space = *oracle->getSpaceForIdentifier(vardecl);
*/
  Space& space = oracle->getSpaceForIdentifier(vardecl);
  bridge::Identifier& bIdent = bridge_domain->addIdentifier(space, vardecl);
  interp->putIdentifier(vardecl, bIdent);
  cerr << "handleCXXConstructIdentifier: Currently identifiers link back to full vardecls. Probably better to link back just to IdentifierInfo.\n";
  return &bIdent;
}

// Function: Add interpretation for binding of Vector identifier to Vector Expression
void handleCXXConstructIdentifierBinding(const clang::VarDecl *vardecl, bridge::Identifier *bv, bridge::Expr *be)
{
  bridge::Binding& binding = *new bridge::Binding(vardecl, *bv, *be);
  interp->putBindingInterp(vardecl, binding);

  /*main.cpp:79:44: error: no matching function for call to 'Interpretation::putBindingInterp(const clang::VarDecl*&, bridge::Binding*&)'
   interp->putBindingInterp(vardecl, binding);
  */
}

// Class: Match Callback class for handling Vector Literal Expressions
class HandlerForCXXConstructLitExpr : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    const auto *litexpr = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("VectorLitExpr");
    ASTContext *context = Result.Context;
    SourceManager &sm = context->getSourceManager();

    // Get space for literal expression
    // Create ast container object for AST Node
    // Create bridge node for lifted AST expression
    // Add (ast container, bridge node) to interpretation
    Space& space = oracle->getSpaceForLitVector(litexpr);
    LitASTNode* ast = new LitASTNode(litexpr);
    bridge::VecLitExpr* br_lit = new bridge::VecLitExpr(space, ast);
    interp->putLitInterp(*ast, *br_lit);
    //cerr << "HandlerForCXXConstructLitExpr: STUB\n";
  }
};

/*********************/

/*******************************
 * Handle Member Call Expression
 *******************************/

/*
Should just inline this.
*/
class HandlerForCXXMemberCallExprRight_DeclRefExpr : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result) {
    const auto *memcallexpr_right_expr = Result.Nodes.getNodeAs<clang::DeclRefExpr>("DeclRefExpr");
    cerr << "HandlerForCXXMemberCallExprRight_DeclRefExpr: Handle Vector Add Member Call Right Arg Expr. STUB.\n";
    ASTContext *context = Result.Context;
    SourceManager &sm = context->getSourceManager();
    // get refd decl
    // handle it
  }
};

/*
*/
class HandlerForCXXMemberCallExprRight_MemberCallExpr : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result) {
    cerr << "HandlerForCXXMemberCallExprRight_MemberCallExpr: Handling Vector Add Member Call, Right Arg Expr is Add Member Call Expr. STUB.\n";
  /*
    a_matcher->match_on_memcallexpr_right_expr()
    if (memcallexpr_right_expr == NULL)
    {
      cerr << "Error in HandlerForCXXMemberCallExprRight_DeclRefExpr::run. No mem call expression pointer.\n";
      return;
    }
    
  */
    cerr << "HandlerForCXXMemberCallExprRight_MemberCallExpr: Done Handling Vector Add Member Call, Right Arg Expr is Add Member Call Expr. STUB.\n";
    return;
  }
};

/**********************/

//Forward-reference handlers for member (left) and argument (expressions) of add application
bridge::Expr *handle_member_expr_of_add_call(const clang::Expr *left, ASTContext& context, SourceManager &sm);
bridge::Expr *handle_arg0_of_add_call(const clang::Expr *right, ASTContext& context, SourceManager &sm);

//CXXMemberCallExpr := CXXMemberCallExprLeft + CXXMemberCallExprRight
class HandlerForCXXConstructAddExpr : public MatchFinder::MatchCallback
{
public:
  //  Get left and right children of add expression and handle them by calls to other handlers
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    cerr << "HandlerForCXXConstructAddExpr: Partial STUB.\n";
    
    ASTContext *context = Result.Context;
    SourceManager &sm = context->getSourceManager();

    const auto *addexpr = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("MemberCallExpr");
    if (addexpr == NULL)
    {
      cerr << "Error in HandlerForCXXConstructAddExpr::run. No add expression pointer\n";
      return;
    }
    //cerr << "HandlerForCXXConstructAddExpr::run\n"; 
    //cerr << "addexpr is\n"; addexpr->dump();

    const clang::Expr *left = addexpr->getImplicitObjectArgument();
    if (!left)
    {
      cerr << "Null left clang pointer\n";
      return;
    }
    //cerr << "HandlerForCXXConstructAddExpr::run, left is elided\n";
    //left->dump();

    bridge::Expr *left_br = handle_member_expr_of_add_call(left, *context, sm);
    if (!left_br)
    {
      cerr << "Got null left bridge pointer (STUB)\n";
      //return;
    }

    const clang::Expr *right = addexpr->getArg(0);
    if (!right)
    {
      cerr << "Got null right clang pointer\n";
      return;
    }
    //cerr << "HandlerForCXXConstructAddExpr::run, right is elided\n";
    //right->dump();


    bridge::Expr *right_br = handle_arg0_of_add_call(right, *context, sm);
    if (!right_br)
    {
      cerr << "Got null right bridge pointer (STUB)\n";
      //return;
    }

    Space &s = oracle->getSpaceForAddExpression(left_br, right_br);
    bridge_domain->addVecAddExpr(s, addexpr, *left_br, *right_br);
  }
};

/***** Handle Right Expr of expr.add(expr) Call Expr ******/

/*
handle_arg0_of_add_call:

match mem call right expr with
  | decl ref expr ==> decl_ref_expr_handler_
  | cxx member call expr ==> addHandler_
*/
class CXXMemberCallExprArg0RightMatcher
{
public:
  CXXMemberCallExprArg0RightMatcher() {

    // case: arg0 is a declaration reference expression
    // action: invoke dre_handler_::run as a match finder action
    const StatementMatcher DeclRefExprPattern = declRefExpr().bind("DeclRefExpr");
    CXXMemberCallExprArg0RightMatcher_.addMatcher(DeclRefExprPattern, &dre_handler_);

    // case: arg0 is a cxx member call expression 
    // action: invoke addHandler_::run as a match finder action  
    const StatementMatcher CXXMemberCallExprPattern = cxxMemberCallExpr();
    CXXMemberCallExprArg0RightMatcher_.addMatcher(CXXMemberCallExprPattern, &mce_handler_);
  }

  void match(const clang::Expr& call_rhs, ASTContext& context)
  {
    //cerr << "CXXMemberCallExprArg0RightMatcher::match start\n";
    CXXMemberCallExprArg0RightMatcher_.match(call_rhs, context);
    //cerr << "CXXMemberCallExprArg0RightMatcher::match finish\n";
  }

private:
  MatchFinder CXXMemberCallExprArg0RightMatcher_;
  HandlerForCXXMemberCallExprRight_DeclRefExpr dre_handler_;
  HandlerForCXXConstructAddExpr mce_handler_;
};

/*
Handle the single argument to an add application 
*/
bridge::Expr *handle_arg0_of_add_call(const clang::Expr *right, ASTContext& context, SourceManager &sm)
{
  //cerr << "Handling Arg[0] (right) of add call. Matching and dispatching.\n";
  CXXMemberCallExprArg0RightMatcher call_right_arg0_matcher;
  call_right_arg0_matcher.match(*right,context);
  cerr << "handle_arg0_of_add_call: STUB Returing Null bridge::Expr.\n";
  return NULL;  
}

// -----------------//

/***** Handle Left, Member, Expr of expr.add(expr) Call Expr ******/

/*
handle_member_expr_of_add_call:

match mem call expr with
  | decl ref expr ==> decl_ref_expr_handler_
  | cxx member call expr ==> addHandler_
*/
class CXXMemberCallExprMemberExprMatcher
{
public:
  CXXMemberCallExprMemberExprMatcher() {

    // case 1: arg0 is a declaration reference expression
    // action: invoke dre_handler_::run as a match finder action
    // case 2: arg0 is a cxx member call expression 
    // action: invoke addHandler_::run as a match finder action  
    const StatementMatcher DeclRefExprPattern = declRefExpr().bind("DeclRefExpr");
//    const StatementMatcher DeclRefExprPattern = memberExpr(parenExpr(declRefExpr().bind("LeftDeclRefExpr")));
    CXXMemberCallExprMemberExprMatcher_.addMatcher(DeclRefExprPattern, &dre_handler_);

    const StatementMatcher CXXMemberCallExprPattern = parenExpr(hasDescendant(cxxMemberCallExpr().bind
    ("MemberCallExpr")));
//    const StatementMatcher CXXMemberCallExprPattern = memberExpr(parenExpr(cxxMemberCallExpr().bind
//    ("MemberCallExpr")));
    CXXMemberCallExprMemberExprMatcher_.addMatcher(CXXMemberCallExprPattern, &mce_handler_);
  }

  void match(const clang::Expr& call_rhs, ASTContext& context)
  {
    //cerr << "CXXMemberCallExprMemberExprMatcher::match start\n";\
    //call_rhs.dump();
    CXXMemberCallExprMemberExprMatcher_.match(call_rhs, context);
    //cerr << "CXXMemberCallExprMemberExprMatcher::match finish\n";
  }

private:
  MatchFinder CXXMemberCallExprMemberExprMatcher_;
  HandlerForCXXMemberCallExprRight_DeclRefExpr dre_handler_;
  HandlerForCXXConstructAddExpr mce_handler_;
};

/*
Handle the single argument to an add application 
*/
bridge::Expr* handle_member_expr_of_add_call(const clang::Expr *left, ASTContext& context, SourceManager& sm)
{
  //cerr << "Handling Member Expr (left) of add call. Matching and dispatching.\n";
  CXXMemberCallExprMemberExprMatcher call_expr_mem_expr_matcher;
  call_expr_mem_expr_matcher.match(*left,context);
  cerr << "handle_member_expr_of_add_call:  STUB returning NULL.\n";
  return NULL; 
}

/********************/

/*
match CXXConstructExpr with
  | literal 3-float initializer ==> lit_handler
  | cxx member call expr (member_expr.add(arg0_expr)==> mem_call_expr_handler
*/
class CXXConstructExprMatcher {
public:
  CXXConstructExprMatcher()
  {
    CXXConstructExprMatcher_.addMatcher(cxxConstructExpr(argumentCountIs(3)), &litHandler_);
    // v1 = v2
    CXXConstructExprMatcher_.addMatcher(cxxConstructExpr(hasDescendant(cxxMemberCallExpr(hasDescendant(memberExpr(hasDeclaration(namedDecl(hasName("vec_add")))))).bind("MemberCallExpr"))), &addHandler_);
  };
  void match(const clang::CXXConstructExpr *consdecl, ASTContext *context) {
    cout << "Pattern Matching on CXXConstructExpr: Start\n";
    CXXConstructExprMatcher_.match(*consdecl, *context);
    cout << "Pattern Matching on CXXConstructExpr: Done\n";
  }
private:
  MatchFinder CXXConstructExprMatcher_;
  HandlerForCXXConstructLitExpr litHandler_;
  HandlerForCXXConstructAddExpr addHandler_;
};

/*
Precondition: consdecl of type CXXConstructExpr* is a pointer to an 
expression, the value of which is being assigned to a variable in a 
declaration statement. 

Explanation: By the time control reaches this code, we are assured 
the argument is an AST node for a Vector-valued expression that is
going to be used to initialize the value of a variable. The purpose 
of this code is to make sure that this C++ expression is "lifted" to
a corresponding expression in the domain/bridge, and that the
interpretation links this code/AST-node to that domain/bridge object.

Postcondition: the return value of this function is pointer to a new 
object of type bridge::Expr; that object is in the bridge; it might
itself represent a complex expression tree; it links back to consdecl;
and the interpretation is updated to like consdecl to the new bridge
object. This function works recursively to make sure that all of the
work of handling the top-level CXXConstructExpr is finished by the 
time this function returns.

Explanation: the way in which this consdecl is turned into a bridge 
object depends on the specific form of the expression being handled.
The cases to be handled include literal and add expressions.
- Vec v1(0.0,0.0,0.0) is a literal expression
- (v1.add(v2)).(v3.add(v4)) is an add expression (recursive)
*/
bridge::Expr *handleCXXConstructExpr(const clang::CXXConstructExpr *consdecl, ASTContext *context, SourceManager &sm)
{
  //cerr << "Pattern matching Vector CXXConstructExpr.\n";
  CXXConstructExprMatcher *matcher = new CXXConstructExprMatcher();
  matcher->match(consdecl, context);
  // postcondition: consdecl now has an interpretation
  // How do we get BI to return to user? Look it up
  // bridge::Expr* bi = interp->getExpr(consdecl);
 
  cerr << "handleCXXConstructExpr: STUB returning NULL OUT)\n";
  return NULL; 
}

/*************************
 * Handle Vector DeclStmts
 *************************/

class VectorDeclStmtHandler : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    /*
    get DeclStatement from matcher
    get context 
    get source manager 
    get handle on variable declaration, vardecl
    be sure it has an initializer, then get the CXXConstructExpr initializer
    get handle on expression used to initialize the variable
    establish interpretation from consdecl to corresponding expression in the domain bridge
    establish interpretation from variable in code to corresponding var object in domain bridge
    finally establish interpretation linking overall declstmt in code to corresponding binding in domain
    */
    const auto *declstmt = Result.Nodes.getNodeAs<clang::DeclStmt>("VectorStatement");
    ASTContext *context = Result.Context;
    SourceManager &sm = context->getSourceManager();
    if (declstmt->isSingleDecl())
    {
      const VarDecl* vardecl = dyn_cast<VarDecl>(declstmt->getSingleDecl());
      const clang::CXXConstructExpr *consdecl;
      if (vardecl->hasInit())
      {
        consdecl = static_cast<const clang::CXXConstructExpr *>(vardecl->getInit());
      }
      else {
        cerr << "VectorDeclStmtHandler.run: add error handling\n";
      }
      //cerr << "Handling vector declaration statement\n";
      bridge::Expr *be = handleCXXConstructExpr(consdecl, context, sm);
      bridge::Identifier *bi = handleCXXConstructIdentifier(vardecl, context, sm);
      handleCXXConstructIdentifierBinding(vardecl, bi, be);
      //cerr << "Done handling vector declaration statement\n\n";
    }
    else
    {
      cerr << "VectorDeclStmtHandler.run: Something's wrong\n";
    }
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
        declStmt(hasDescendant(varDecl(hasDescendant(cxxConstructExpr(hasType(asString("class Vec"))))))).bind("VectorStatement");
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
    bool consistent = bridge_domain->isConsistent();
    cerr << (consistent ? "STUB Analysis result: Good\n" : "STUB: Bad\n");
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
  bridge_domain = new Bridge();
  bridge_domain->addSpace("S1");
  bridge_domain->addSpace("S2");
  interp = new Interpretation();
  oracle = new Oracle(*bridge_domain);
  return Tool.run(newFrontendActionFactory<MyFrontendAction>().get());
}