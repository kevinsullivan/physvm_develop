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

unordered_map<const clang::Expr *, const ExprASTNode *> expr_wrappers;
unordered_map<const clang::Stmt *, const ExprASTNode *> stmt_wrappers;
unordered_map<const clang::Decl *, const ExprASTNode *> decl_wrappers;

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

/*****************************
 * CXXConstructExpr (LITERALS) 
 *****************************/

// Class: Match Callback class for handling Vector Literal Expressions
class HandlerForCXXConstructLitExpr : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    //cerr << "HandlerForCXXConstructLitExpr. AST:\n";
    const clang::CXXConstructExpr *litexpr /*consdecl*/ = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("VectorLitExpr");

    //ASTContext *context = Result.Context;
    //SourceManager &sm = context->getSourceManager();

    // Get space for literal expression
    // Create ast container object for AST Node
    // Create bridge node for lifted AST expression
    // Add (ast container, bridge node) to interpretation
    Space &space = oracle->getSpaceForLitVector(litexpr);
    LitASTNode *litexpr_wrapper = new LitASTNode(litexpr);
    expr_wrappers.insert(std::make_pair(litexpr, litexpr_wrapper));
    bridge::Expr &br_lit = bridge_domain->addVecLitExpr(space, litexpr_wrapper);
    interp->putExpressionInterp(*litexpr_wrapper, br_lit);
    // assert: postcondition (inter def for consdecl) satisfied
    //cerr << "END HandlerForCXXConstructLitExpr\n";
  }
};

/*******************************
 * Handle Member Call Expression
 *******************************/

//Forward-reference handlers for member (left) and argument (expressions) of add application
const bridge::Expr *handle_member_expr_of_add_call(const clang::Expr *left, ASTContext &context, SourceManager &sm);
const bridge::Expr *handle_arg0_of_add_call(const clang::Expr *right, ASTContext &context, SourceManager &sm);

const bridge::Expr *handleMemberCallExpr(const CXXMemberCallExpr *addexpr, ASTContext *context, SourceManager &sm)
{
  const clang::Expr *left = addexpr->getImplicitObjectArgument();
  if (!left)
  {
    cerr << "handleMemberCallExpr:: Null left clang pointer\n";
    return NULL;
  }
  //cerr << "handleMemberCallExpr::run, left is elided\n";
  //left->dump();

  const clang::Expr *right = addexpr->getArg(0);
  if (!right)
  {
    cerr << "Got null right clang pointer\n";
    return NULL;
  }
  //cerr << "HandlerForCXXConstructAddExpr::run, right is elided\n";
  //right->dump();

  // KEVIN

  const bridge::Expr *left_br = handle_member_expr_of_add_call(left, *context, sm);
  if (!left_br)
  {
    cerr << "Got null left bridge pointer (STUB)\n";
    //return;
  }

  const bridge::Expr *right_br = handle_arg0_of_add_call(right, *context, sm);
  if (!right_br)
  {
    cerr << "Got null right bridge pointer (STUB)\n";
    //return;
  }

  // pre-condition: these objects are already in these maps
  const ExprASTNode *left_wrapper = expr_wrappers[left];
  const ExprASTNode *right_wrapper = expr_wrappers[right];
  if (left_wrapper == NULL || right_wrapper == NULL)
  {
    cerr << "BAD WRAPPER\n";
  }

  VectorAddExprASTNode *wrapper = new VectorAddExprASTNode(addexpr, left_wrapper, right_wrapper);
  Space &s = oracle->getSpaceForAddExpression(left_br, right_br);
  const bridge::Expr &br_add_expr = bridge_domain->addVecAddExpr(s, wrapper, *left_br, *right_br);
  interp->putExpressionInterp(*wrapper, br_add_expr);
  expr_wrappers.insert(std::make_pair(addexpr, wrapper));
  return &br_add_expr;
}

/*
TODO: CONSIDER inlining this code.
*/
class HandlerForCXXMemberCallExprRight_DeclRefExpr : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    const auto *declRefExpr = Result.Nodes.getNodeAs<clang::DeclRefExpr>("DeclRefExpr");
    cerr << "HandlerForCXXMemberCallExprRight_DeclRefExpr: Got declRefExpr = " << std::hex << declRefExpr << "\n";
    // ASTContext *context = Result.Context;
    // SourceManager &sm = context->getSourceManager();
    const VarDeclRefASTNode *wrapper = new VarDeclRefASTNode(declRefExpr);
    expr_wrappers.insert(std::make_pair(declRefExpr, wrapper));
    bridge::Expr &be = bridge_domain->addVecVarExpr(wrapper);
    interp->putExpressionInterp(*wrapper, be);
    // postcondition, be can now be found through interpret with wrapped declRefExpr as key
  }
};

//CXXMemberCallExpr := CXXMemberCallExprLeft + CXXMemberCallExprRight
class HandlerForCXXAddMemberCall : public MatchFinder::MatchCallback
{
public:
  //  Get left and right children of add expression and handle them by calls to other handlers
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    cerr << "HandlerForCXXAddMemberCall.\n";

    ASTContext *context = Result.Context;
    SourceManager &sm = context->getSourceManager();

    const CXXMemberCallExpr *memcall = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("MemberCallExpr");
    if (memcall == NULL)
    {
      cerr << "Error in HandlerForCXXAddMemberCall::run. No memcall pointer\n";
      return;
    }

    const clang::Expr *left = memcall->getImplicitObjectArgument();
    if (!left)
    {
      cerr << "handleMemberCallExpr:: Null left clang pointer\n";
      return;
    }
    //cerr << "handleMemberCallExpr::run, left is elided\n";
    //left->dump();

    const clang::Expr *right = memcall->getArg(0);
    if (!right)
    {
      cerr << "Got null right clang pointer\n";
      return;
    }
    //cerr << "HandlerForCXXAddMemberCall::run, right is elided\n";
    //right->dump();

    // KEVIN

    const bridge::Expr *left_br = handle_member_expr_of_add_call(left, *context, sm);
    if (!left_br)
    {
      cerr << "Got null left bridge pointer (STUB)\n";
      //return;
    }

    const bridge::Expr *right_br = handle_arg0_of_add_call(right, *context, sm);
    if (!right_br)
    {
      cerr << "Got null right bridge pointer (STUB)\n";
      //return;
    }

    // pre-condition: these objects are already in these maps
    const ExprASTNode *left_wrapper = expr_wrappers[left];
    const ExprASTNode *right_wrapper = expr_wrappers[right];
    if (left_wrapper == NULL || right_wrapper == NULL)
    {
      cerr << "BAD WRAPPER\n";
    }

    VectorAddExprASTNode *ast = new VectorAddExprASTNode(memcall, left_wrapper, right_wrapper);
    expr_wrappers.insert(std::make_pair(memcall, ast));
    Space &s = oracle->getSpaceForAddExpression(left_br, right_br);
    const bridge::Expr &br_add_expr = bridge_domain->addVecAddExpr(s, ast, *left_br, *right_br);
    interp->putExpressionInterp(*ast, br_add_expr);
  }
};

//CXXMemberCallExpr := CXXMemberCallExprLeft + CXXMemberCallExprRight
class HandlerForCXXConstructAddExpr : public MatchFinder::MatchCallback
{
public:
  //  Get left and right children of add expression and handle them by calls to other handlers
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    cerr << "!!!!!!!!!!!!!!!!!!!!!!!! HandlerForCXXConstructAddExpr !!!!!!!!!!!!!!!!!!!!!!.\n";

    ASTContext *context = Result.Context;
    SourceManager &sm = context->getSourceManager();

    const CXXConstructExpr *consdecl = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("VectorAddExpr");
    if (consdecl == NULL)
    {
      cerr << "Error in HandlerForCXXConstructAddExpr::run. No constructor declaration pointer\n";
      return;
    }

    // match on member call expr, assume "Expr* mce" back

    const CXXMemberCallExpr *addexpr = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("MemberCallExpr");
    if (addexpr == NULL)
    {
      cerr << "Error in HandlerForCXXConstructAddExpr::run. No add expression pointer\n";
      return;
    }

    //cerr << "HandlerForCXXConstructAddExpr::run\n";
    //cerr << "addexpr is\n"; addexpr->dump();

    const bridge::Expr *memberCallExpr = handleMemberCallExpr(addexpr, context, sm);
    const ExprASTNode* addexprWrapper =expr_wrappers[addexpr]; 
    const AddConstructASTNode* wrapper = new AddConstructASTNode(consdecl, addexprWrapper);      
    expr_wrappers.insert(std::make_pair(consdecl,wrapper));
    interp->putExpressionInterp(*wrapper, *memberCallExpr);
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
    cerr << "CXXMemberCallExprArg0Matcher::match start\n";
    CXXMemberCallExprArg0Matcher_.match(call_rhs, context);
    cerr << "CXXMemberCallExprArg0Matcher::match finish\n";
  }

private:
  MatchFinder CXXMemberCallExprArg0Matcher_;
  HandlerForCXXMemberCallExprRight_DeclRefExpr dre_handler_;
  HandlerForCXXAddMemberCall mce_handler_;
};

/*
Handle the single argument to an add application 
*/
const bridge::Expr *handle_arg0_of_add_call(const clang::Expr *right, ASTContext &context, SourceManager &sm)
{
  cerr << "handle_arg0_of_add_call (match).\n";
  right->dump(); // KJS
  CXXMemberCallExprArg0Matcher call_right_arg0_matcher;
  call_right_arg0_matcher.match(*right, context);

  // postcondition: look up right in interp and return corresponding value
  const ExprASTNode *wrapper = new ExprASTNode(right);
  const bridge::Expr *expr = interp->getExpressionInterp(*wrapper);
  expr_wrappers.insert(std::make_pair(right, wrapper));
  //cerr << "END: handle_arg0_of_add_call: returning " << std::hex << expr << ". STUB?\n";
  return expr;
}

/*
handle_member_expr_of_add_call:

match mem call expr with
  | decl ref expr ==> decl_ref_expr_handler_
  | cxx member call expr ==> addHandler_
*/
class CXXMemberCallExprMemberExprMatcher
{
public:
  CXXMemberCallExprMemberExprMatcher()
  {

    // case 1: arg0 is a declaration reference expression
    // action: invoke dre_handler_::run as a match finder action
    // case 2: arg0 is a cxx member call expression
    // action: invoke addHandler_::run as a match finder action
    const StatementMatcher DeclRefExprPattern = declRefExpr().bind("DeclRefExpr");
    //const StatementMatcher DeclRefExprPattern = memberExpr(parenExpr(declRefExpr().bind("LeftDeclRefExpr")));
    CXXMemberCallExprMemberExprMatcher_.addMatcher(DeclRefExprPattern, &dre_handler_);

    const StatementMatcher CXXMemberCallExprPattern = parenExpr(hasDescendant(cxxMemberCallExpr().bind("MemberCallExpr")));
    CXXMemberCallExprMemberExprMatcher_.addMatcher(CXXMemberCallExprPattern, &mce_handler_);
  }

  void match(const clang::Expr &call_rhs, ASTContext &context)
  {
    //cerr << "CXXMemberCallExprMemberExprMatcher::match start\n";
    //call_rhs.dump();
    CXXMemberCallExprMemberExprMatcher_.match(call_rhs, context);
    //cerr << "CXXMemberCallExprMemberExprMatcher::match finish\n";
  }

private:
  MatchFinder CXXMemberCallExprMemberExprMatcher_;
  HandlerForCXXMemberCallExprRight_DeclRefExpr dre_handler_;
  HandlerForCXXAddMemberCall mce_handler_;
};

/*
Handle the single argument to an add application 
*/
const bridge::Expr *handle_member_expr_of_add_call(const clang::Expr *left, ASTContext &context, SourceManager &sm)
{
  cerr << "handle_member_expr_of_add_call\n";
  if (left == NULL)
  {
    cerr << "Null argument\n";
  }
  else
    left->dump();
  CXXMemberCallExprMemberExprMatcher call_expr_mem_expr_matcher;
  call_expr_mem_expr_matcher.match(*left, context);

  // postcondition: look up left in interp and return corresponding value
  const ExprASTNode *wrapper = new ExprASTNode(left);
  const bridge::Expr *expr = interp->getExpressionInterp(*wrapper);
  expr_wrappers.insert(std::make_pair(left, wrapper));
  //cerr << "END: handle_member_expr_of_add_call: returning " << std::hex << expr << ". STUB?\n";
  return expr;
}

/********************/

/*
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
    // v1 = v2
    CXXConstructExprMatcher_.addMatcher(cxxConstructExpr(hasDescendant(cxxMemberCallExpr(hasDescendant(memberExpr(hasDeclaration(namedDecl(hasName("vec_add")))))).bind("MemberCallExpr"))).bind("VectorAddExpr"), &addHandler_);
  };
  void match(const clang::CXXConstructExpr *consdecl, ASTContext *context)
  {
    cout << "START: Pattern Matching on CXXConstructExpr: Start\n";
    CXXConstructExprMatcher_.match(*consdecl, *context);
    cout << "DONE: Pattern Matching on CXXConstructExpr: Start\n";
    // assert: interp now defined for consdecl

    //cout << "END Pattern Matching on CXXConstructExpr\n";
  }

private:
  MatchFinder CXXConstructExprMatcher_;
  HandlerForCXXConstructLitExpr litHandler_;
  HandlerForCXXConstructAddExpr addHandler_;
};

//--------------------

//const bridge::Expr* handleMemberCall

//--------------------

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

bridge::Expr *handleCXXConstructExpr(const clang::CXXConstructExpr *consdecl, ASTContext *context, SourceManager &sm)
{
  //cerr << "handleCXXConstructExpr: Start handleCXXConstructExpr\n";
  //cerr << "Pattern matching Vector CXXConstructExpr.\n";
  CXXConstructExprMatcher matcher;
  matcher.match(consdecl, context);
  // postcondition: consdecl now has an interpretation
  // How do we get BI to return to user? Look it up
  // bridge::Expr* bi = interp->getExpr(consdecl);
  // TO DO: Architectural change means we need to wrap consdecl to map it

  const ExprASTNode *ast = new ExprASTNode(consdecl);   // TODO -- BETTER TYPE!
  bridge::Expr *be = interp->getExpressionInterp(*ast);
  //cerr << "handleCXXConstructExpr: Returning Expr at " << std::hex << be << "\n";
  return be;
}
*/

const bridge::Expr *handleCXXDeclStmt(const clang::CXXConstructExpr *consdecl, ASTContext *context, SourceManager &sm)
{
  //cerr << "handleCXXConstructExpr: Start handleCXXConstructExpr\n";
  //cerr << "Pattern matching Vector CXXConstructExpr.\n";
  CXXConstructExprMatcher matcher;
  matcher.match(consdecl, context);
  // postcondition: consdecl now has an interpretation
  // How do we get BI to return to user? Look it up
  // bridge::Expr* bi = interp->getExpr(consdecl);
  // TO DO: Architectural change means we need to wrap consdecl to map it

  const ExprASTNode *wrapper = new ExprASTNode(consdecl); // TODO -- BETTER TYPE!
  const bridge::Expr *be = interp->getExpressionInterp(*wrapper);
  expr_wrappers.insert(std::make_pair(consdecl, wrapper));
  //cerr << "handleCXXConstructExpr: Returning Expr at " << std::hex << be << "\n";
  return be;
}

/*************************
 * Handle Vector DeclStmts
 *************************/

class VectorDeclStmtHandler : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    const clang::DeclStmt *declstmt = Result.Nodes.getNodeAs<clang::DeclStmt>("VectorDeclStatement");
    const clang::CXXConstructExpr *consdecl = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("CXXConstructExpr");
    const clang::VarDecl *vardecl = Result.Nodes.getNodeAs<clang::VarDecl>("VarDecl");

    ASTContext *context = Result.Context;
    SourceManager &sm = context->getSourceManager();

    cerr << "VectorDeclStmtHandler:: Decl Statement is \n"; declstmt->dump();
    cerr << "VectorDeclStmtHandler:: ConstructorExpr is \n"; consdecl->dump();
    cerr << "VectorDeclStmtHandler:: vardecl is\n"; vardecl->dump();


    // IDENTIFIER
    //
    Space &space = oracle->getSpaceForIdentifier(vardecl);
    IdentifierASTNode *ast_container = new IdentifierASTNode(vardecl);
    decl_wrappers.insert(std::make_pair(vardecl, ast_container));
    bridge::Identifier &bi = bridge_domain->addIdentifier(space, ast_container);
    interp->putIdentInterp(*ast_container, bi);
    //cerr << "END: handleCXXConstructIdentifier\n";

    // CONSTRUCTOR (Lit | Add)
    //
    cerr << "VectorDeclStmtHandler: matching on consdecl\n";
    CXXConstructExprMatcher matcher;
    matcher.match(consdecl, context);
    const ExprASTNode *wrapper = new ExprASTNode(consdecl); // TODO -- BETTER TYPE!
    expr_wrappers.insert(std::make_pair(consdecl, wrapper));
    const bridge::Expr *be = interp->getExpressionInterp(*wrapper);
    if (be == NULL)
    {
      cerr << "NULL expression in DeclStmt.\n";
    }
    cerr << "VectorDeclStmtHandler: done matching on consdecl\n";

    cerr << "Bridge expressions:\n";
    bridge_domain->dumpExpressions(); // print contents on cerr
    cerr << "Bridge Identifiers\n";
    bridge_domain->dumpIdentifiers(); // print contents on cerr
    cerr << "Bridge Bindings\n";
    bridge_domain->dumpBindings(); // print contents on cerr
    cerr << "InterpExpressions\n";
    interp->dumpExpressions();


    // BINDING
    //
    BindingASTNode *declstmt_wrapper = new BindingASTNode(declstmt);
    stmt_wrappers.insert(std::make_pair(declstmt, declstmt_wrapper));
    bridge::Binding &binding = bridge_domain->addBinding(declstmt_wrapper, bi, *be);
    interp->putBindingInterp(declstmt_wrapper, binding);
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
  Tool.run(newFrontendActionFactory<MyFrontendAction>().get());
  cerr << "Identifiers\n";
  bridge_domain->dumpIdentifiers();
  cerr << "Expressions\n";
  bridge_domain->dumpExpressions();
  cerr << "Bindings\n";
  bridge_domain->dumpBindings();
}