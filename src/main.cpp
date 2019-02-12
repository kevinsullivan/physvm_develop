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
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include <iostream>
#include <string>

#include "Code.h"
#include "Coords.h"
#include "CodeToCoords.h"
#include "Oracle.h"
#include "Domain.h"
#include "CoordsToDomain.h"
#include "Interpretation.h"

using namespace std;

using namespace llvm;
using namespace clang;
using namespace clang::ast_matchers;
using namespace clang::driver;
using namespace clang::tooling;

/**************************************************
Fundamental data structure constructed by this tool
***************************************************/

interp::Interpretation interp_;

/*
Sharing data via global variables is a bad idea, but we'll
do it to get a working system. These variables are initialized
in main() and updated during the parse tree traversal, as AST
node handlers are triggered.
*/

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

create a domain variable object
add interpretation from vardecl to domain variable object
maybe return a bool or something to indicate success or failure?
*/
domain::Identifier *handleCXXConstructIdentifier(const VarDecl *vardecl,
                                                 ASTContext *context,
                                                 SourceManager &sm) {
 return interp_.mkVecIdent(vardecl);

/*
  cerr << "START domain::Identifier *handleCXXConstructIdentifier. VarDecl is \n";
  if (!vardecl) { 
      cerr << "domain::Identifier *handleCXXConstructIdentifier: Null vardecl\n";}
  else { 
      vardecl->dump(); 
    }

  domain::Space &space = interp_.oracle_->getSpaceForIdentifier(vardecl);
  coords::VecIdent *vardecl_wrapper = new coords::VecIdent(vardecl);
  cerr << "handleCXXConstructIdentifier: Created vardecl wrapper at " << std::hex << vardecl_wrapper << " for clang vardecl at " << std::hex << vardecl << "; toString is : " << vardecl_wrapper->toString() << "\n";
  interp_.code2coords_->decl_wrappers.insert(std::make_pair(vardecl, vardecl_wrapper));
  domain::Identifier* br_id = interp_.domain_->addIdentifier(space, vardecl_wrapper);
  interp_.coords2dom_->putIdentifierInterp(vardecl_wrapper, br_id);
  cerr << "END domain::Identifier *handleCXXConstructIdentifier\n";

  //  domain::Identifier *bIdent = new Identifier(vardecl);
  //  interp->putIdentifier(vardecl, bIdent);
  //  cout << "Created domain identifier\n";
  //  return bIdent;
  */
}

// Function: Add interpretation for binding of Vector identifier to Vector
// Expression
void handleCXXConstructIdentifierBinding(
        const clang::DeclStmt* declstmt,
        const domain::Identifier *bv,
        const domain::Expr *be) {
  cerr << "START: handleCXXConstructIdentifierBinding: Adding interp for binding\n.";
  if (!be || !bv) { cerr << "handleCXXConstructIdentifierBinding: null argument\n";}
  
  
  const coords::VecIdent* bv_wrapper = bv->getVarDeclWrapper();
  cerr << "handleCXXConstructIdentifierBinding: identifier at " << std::hex << bv << " wrapped addr is " << std::hex << bv_wrapper->getASTNode() << "\n";
  cerr << "handleCXXConstructIdentifierBinding: wrapped dump is \n"; bv_wrapper->getASTNode()->dump();
  cerr << "handleCXXConstructIdentifierBinding: name is " << bv_wrapper->toString() << "\n";
  cerr<<"On to the next bit\n";
  






  const coords::ExprASTNode* be_wrapper = be->getExprASTNode();

  coords::BindingASTNode *declstmt_wrapper = new coords::BindingASTNode(declstmt, bv_wrapper, be_wrapper);
  interp_.code2coords_->stmt_wrappers.insert(std::make_pair(declstmt, declstmt_wrapper));
  domain::Binding &binding =
      interp_.domain_->addBinding(declstmt_wrapper, bv, be);
  interp_.coords2dom_->putBindingInterp(declstmt_wrapper, binding);
  cerr << "DONE: handleCXXConstructIdentifierBinding: Adding interp for binding\n";
}

// Class: Match Callback class for handling Vector Literal Expressions
class HandlerForCXXConstructLitExpr : public MatchFinder::MatchCallback {
public:
  virtual void run(const MatchFinder::MatchResult &Result) {
    const auto *litexpr =
        Result.Nodes.getNodeAs<clang::CXXConstructExpr>("VectorLitExpr");
    cerr << "START HandlerForCXXConstructLitExpr::run on " << std::hex << litexpr << "\n";
    ASTContext *context = Result.Context;
    SourceManager &sm = context->getSourceManager();
    domain::Space &space = interp_.oracle_->getSpaceForLitVector(litexpr);
    coords::LitASTNode *litexpr_wrapper = new coords::LitASTNode(litexpr);  
    interp_.code2coords_->expr_wrappers.insert(std::make_pair(litexpr, litexpr_wrapper));
    domain::Expr* br_lit = interp_.domain_->addVecLitExpr(space, litexpr_wrapper);
    interp_.coords2dom_->putExpressionInterp(litexpr_wrapper, br_lit);
    cerr << "DONE HandlerForCXXConstructLitExpr::run\n";
  }
};

/*********************/
// BEGIN OF HANDLER SECTION FOR VEC_ADD APPLICATION
/*********************/
// Handlers classes that inheritated from the MatchFinder::MatchCallbacks
// There should be 4 of these
// HandlerForDeclRefExpr
// HandlerForMemberExpr
// HandlerForCXXMemberCallExprLeft
// HandlerForCXXMemberCallExprRight

/*********************/
// BEGIN OF FORWARD DECLARATION FOR ALL THE HANDLERS AND MATCHERS
/*********************/

// declarations of the Handlers
class HandlerForDeclRefExpr;
class HandlerForMemberExpr;
class HandlerForCXXMemberCallExprLeft;
class HandlerForCXXMemberCallExprRight;
class HandlerForCXXMemberCallExpr;

// declarations of the Matchers
class CXXMemberCallExprLeftMatcher;
class CXXMemberCallExprRightMatcher;
class MemberExprMatcher;

/*********************/
// END OF FORWARD DECLARATION FOR ALL THE HANDLERS AND MATCHERS
/*********************/

/*********************/
// BEGIN OF DECLARATION FOR ALL THE HANDLERS AND MATCHERS
/*********************/

// declarations of the Handlers
class HandlerForDeclRefExpr : public MatchFinder::MatchCallback {
public:
  HandlerForDeclRefExpr() {}
  virtual void run(const MatchFinder::MatchResult &Result);
};

class HandlerForMemberExpr : public MatchFinder::MatchCallback {
public:
  HandlerForMemberExpr() {}
  virtual void run(const MatchFinder::MatchResult &Result);
};

class HandlerForCXXMemberCallExprLeft : public MatchFinder::MatchCallback {
public:
  HandlerForCXXMemberCallExprLeft() {}
  virtual void run(const MatchFinder::MatchResult &Result);
};

class HandlerForCXXMemberCallExprRight : public MatchFinder::MatchCallback {
public:
  HandlerForCXXMemberCallExprRight() {}
  virtual void run(const MatchFinder::MatchResult &Result);
};

class HandlerForCXXMemberCallExpr : public MatchFinder::MatchCallback {
public:
  HandlerForCXXMemberCallExpr() {}
  virtual void run(const MatchFinder::MatchResult &Result);
};

// declarations of the Matchers-----------------------------------

// Precondition: when you have a big node that contains a CXXMembercallExpr
// as sub node, use this matcher to get the CXXMembercallExpr node and it will
// send the right handler for it.

class CXXMemberCallExprMatcher {
public:
  CXXMemberCallExprMatcher();
  void match(const clang::Expr *node, ASTContext *context);

private:
  MatchFinder cxxMemberCallExprMatcher_;
  HandlerForCXXMemberCallExpr cxxMemberCallExprHandler;
};

class CXXMemberCallExprLeftMatcher {
public:
  CXXMemberCallExprLeftMatcher();
  void match(const clang::Expr *call_lhs, ASTContext *context);

private:
  MatchFinder CXXMemberCallExprLeftMatcher_;
  HandlerForMemberExpr memberexprHandler;
};

class CXXMemberCallExprRightMatcher {
public:
  CXXMemberCallExprRightMatcher();
  void match(const clang::Expr *call_rhs, ASTContext *context);

private:
  MatchFinder CXXMemberCallExprRightMatcher_;
  HandlerForDeclRefExpr declRefExprHandler;
  HandlerForCXXMemberCallExpr cxxMemberCallExprHandler;
};

class MemberExprMatcher {

public:
  MemberExprMatcher();
  void match(const clang::Expr *membernode, ASTContext *context);

private:
  MatchFinder MemberExprMatcher_;
  HandlerForDeclRefExpr declRefExprHandler;
  HandlerForCXXMemberCallExpr cxxMemberCallExprHandler;
};

/*********************/
// END OF DECLARATION FOR ALL THE HANDLERS AND MATCHERS
/*********************/

/*********************/
// BEGIN OF IMPLEMENTATION FOR ALL THE HANDLERS AND MATCHERS OF OBJECTS THAT
// APPEAR IN THE GRAMMAR
/*********************/

// BEGIN OF HANDLER HELPER FUNCTIONS

domain::Expr *handle_left_of_add_call(const clang::Expr *left,
                                      ASTContext *context) {
  cout << "Handling LEFT of add call----Left Hand Side\n";
  CXXMemberCallExprLeftMatcher *leftmatcher =
      new CXXMemberCallExprLeftMatcher();
  leftmatcher->match(left, context);
}

domain::Expr *handle_right_of_add_call(const clang::Expr *right,
                                       ASTContext *context) {
  cout << "Handling RIGHT of add call----Right Hand Side\n";
  CXXMemberCallExprRightMatcher *rightmatcher =
      new CXXMemberCallExprRightMatcher();
  rightmatcher->match(right, context);

  // STUB OUT the implementation for the domain::Expr object
  return NULL;
}

// END OF HANDLER HELPER FUNCTIONS

void HandlerForDeclRefExpr::run(const MatchFinder::MatchResult &Result) {
  const auto *declRefexpr =
      Result.Nodes.getNodeAs<clang::DeclRefExpr>("DeclRefExpr");
  if (declRefexpr != NULL) {
    cout << ">>>>>>>>>>>>>>>DeclRefExpr on the right hand side "
            "found>>>>>>>>>>>>>>>\n";
    cout << "The name of this class should be DeclRefExpr, in fact it is "
         << declRefexpr->getStmtClassName() << endl;
    // TODO do return node from the look up in the domain
  } else {
    cout << "DeclRefExpr is NULL!\n" << endl;
    return;
  }
}

void HandlerForMemberExpr::run(const MatchFinder::MatchResult &Result) {

  const auto *declRefexpr =
      Result.Nodes.getNodeAs<clang::DeclRefExpr>("DeclRefExpr");
  if (declRefexpr != NULL) {
    cout << "<<<<<<<<<<<DeclRefExpr on the left hand side found<<<<<<<<<<<\n";
    cout << "The name of this class should be DeclRefExpr, in fact it is "
         << declRefexpr->getStmtClassName() << endl;
    // TODO do recursion on this node
  }

  const auto *cxxMemberCallExpr =
      Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("CXXMemberCallExpr");
  if (cxxMemberCallExpr != NULL) {
    cout
        << " The name of this class should be CXXMemberCallExpr, in fact it is "
        << cxxMemberCallExpr->getStmtClassName() << endl;
    CXXMemberCallExprMatcher *matcher = new CXXMemberCallExprMatcher();
    matcher->match(cxxMemberCallExpr, Result.Context);
  }
}

void HandlerForCXXMemberCallExprRight::run(
    const MatchFinder::MatchResult &Result) {

  const auto *declRefexpr =
      Result.Nodes.getNodeAs<clang::DeclRefExpr>("DeclRefExpr");
  if (declRefexpr != NULL) {
    cout << "The name of this class should be DeclRefExpr, in fact it is "
         << declRefexpr->getStmtClassName() << endl;
    // TODO do recursion on this node
  }

  const auto *cxxMemberCallExpr =
      Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("CXXMemberCallExpr");
  if (cxxMemberCallExpr != NULL) {
    cout
        << " The name of this class should be CXXMemberCallExpr, in fact it is "
        << cxxMemberCallExpr->getStmtClassName() << endl;
    CXXMemberCallExprMatcher *matcher = new CXXMemberCallExprMatcher();
    matcher->match(cxxMemberCallExpr, Result.Context);
  }
}

void HandlerForCXXMemberCallExpr::run(const MatchFinder::MatchResult &Result) {
  const auto *addexpr =
      Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("CXXMemberCallExpr");
  if (addexpr == NULL) {
    cout << "Error in HandlerForCXXConstructAddExpr::run. No add expression "
            "pointer\n";
    return;
  }
  ASTContext *context = Result.Context;
  SourceManager &sm = context->getSourceManager();
  // cout << "Handling Vector Add (Member Call) Expr. Recurse on implicit
  // parameter and argument. STUB.\n";
  cout << "===================Entered the top-level node -- CXXMemberCallExpr "
          "================"
       << endl;
  cout << "parent class Name is " << addexpr->getStmtClassName() << endl;
  // const clang::Expr *left = addexpr->getImplicitObjectArgument(); This does
  // not give us what we want
  const auto *temp = *(addexpr->child_begin());
  const clang::Expr *left = static_cast<const clang::Expr *>(temp);
  // cout<<"Left child class Name is "<<left->getStmtClassName()<<endl;

  const clang::Expr *right = addexpr->getArg(0);
  // cout<<"Right child class Name is "<<right->getStmtClassName()<<endl;

  if (!left) {
    cout << "Null left clang pointer\n";
    return;
  } else if (!right) {
    cout << "Null right clang pointer\n";
    return;
  }

  domain::Expr *left_br = handle_left_of_add_call(left, context);
  domain::Expr *right_br = handle_right_of_add_call(right, context);

  if (!left) {
    cout << "Null left domain pointer\n";
    return;
  } else if (!right) {
    cout << "Null right domain pointer\n";
    return;
  }

  //  domain::Space &s = interp_.coords2dom_->getSpaceForAddExpression(left_br, right_br);
  //  domain->addVecAddExpr(s, addexpr, *left_br, *right_br);

  cerr << "STUB: HandlerForCXXMemberCallExpr::run(const "
          "MatchFinder::MatchResult &Result)\n";
  // insert this into interpretation table
}

////////////////////MATCHER
///IMPLEMENTATION////////////////////////////////////////////

/*********************/
// BEGIN OF MATCHER SECTION FOR VEC_ADD APPLICATION
/*********************/
// There should exist the matchers for the following kind
// CXXMemberCallExprMatcher
// CXXMemberCallExprLeftMatcher
// CXXMemberCallExprRightMatcher
// MemberExprMatcher

CXXMemberCallExprMatcher::CXXMemberCallExprMatcher() {
  StatementMatcher cxxMemberCallExprMatcherOuterPattern = cxxConstructExpr(
      hasDescendant(cxxMemberCallExpr(hasDescendant(memberExpr(hasDeclaration(
                                          namedDecl(hasName("vec_add"))))))
                        .bind("CXXMemberCallExpr")));
  cxxMemberCallExprMatcher_.addMatcher(cxxMemberCallExprMatcherOuterPattern,
                                       &cxxMemberCallExprHandler);

  StatementMatcher cxxMemberCallExprMatcherInnerPattern =
      cxxMemberCallExpr().bind("CXXMemberCallExpr");
  cxxMemberCallExprMatcher_.addMatcher(cxxMemberCallExprMatcherInnerPattern,
                                       &cxxMemberCallExprHandler);
}
void CXXMemberCallExprMatcher::match(const clang::Expr *node,
                                     ASTContext *context) {
  cxxMemberCallExprMatcher_.match(*node, *context);
}

CXXMemberCallExprLeftMatcher::CXXMemberCallExprLeftMatcher() {

  // On the lhs, the node is MemberExpr
  // there are 2 possible cases of the MemberExpr children
  // case 1 -- DeclRefExpr
  StatementMatcher declRefExprMatcher =
      memberExpr(hasDescendant(declRefExpr().bind("DeclRefExpr")));

  CXXMemberCallExprLeftMatcher_.addMatcher(declRefExprMatcher,
                                           &memberexprHandler);

  // case 2 -- innerCXXMemberCallExpr
  StatementMatcher innerCXXMemberCallExprMatcher =
      memberExpr(hasDescendant(cxxMemberCallExpr().bind("CXXMemberCallExpr")));

  CXXMemberCallExprLeftMatcher_.addMatcher(innerCXXMemberCallExprMatcher,
                                           &memberexprHandler);
}

void CXXMemberCallExprLeftMatcher::match(const clang::Expr *call_lhs,
                                         ASTContext *context) {
  CXXMemberCallExprLeftMatcher_.match(*call_lhs, *context);
}

CXXMemberCallExprRightMatcher::CXXMemberCallExprRightMatcher() {
  // on the rhs
  // matcher to retrieve declRefexpr with ID -- DeclRefExpr
  StatementMatcher declRefExprMatcher = declRefExpr().bind("DeclRefExpr");
  CXXMemberCallExprRightMatcher_.addMatcher(declRefExprMatcher,
                                            &declRefExprHandler);

  // matcher to retrieve CXXMemberCallExpr with ID -- CXXMemberCallExpr
  StatementMatcher innerCXXMemberCallExprMatcher =
      cxxMemberCallExpr(hasDescendant(memberExpr(
                            hasDeclaration(namedDecl(hasName("vec_add"))))))
          .bind("CXXMemberCallExpr");

  CXXMemberCallExprRightMatcher_.addMatcher(innerCXXMemberCallExprMatcher,
                                            &cxxMemberCallExprHandler);
}

void CXXMemberCallExprRightMatcher::match(const clang::Expr *call_rhs,
                                          ASTContext *context) {
  CXXMemberCallExprRightMatcher_.match(*call_rhs, *context);
}

MemberExprMatcher::MemberExprMatcher() {

  StatementMatcher declRefExprMatcher = declRefExpr().bind("DeclRefExpr");

  MemberExprMatcher_.addMatcher(declRefExprMatcher, &declRefExprHandler);

  StatementMatcher innerCXXMemberCallExprMatcher =
      parenExpr(hasDescendant(cxxMemberCallExpr().bind("CXXMemberCallExpr")));

  MemberExprMatcher_.addMatcher(innerCXXMemberCallExprMatcher,
                                &cxxMemberCallExprHandler);
}

void MemberExprMatcher::match(const clang::Expr *cxxmembernode,
                              ASTContext *context) {
  MemberExprMatcher_.match(*cxxmembernode, *context);

  cout << "===========Inside the MemberExpr Matcher ============" << endl;
}

/*********************/
// END OF IMPLEMENTATION FOR ALL THE HANDLERS AND MATCHERS OF OBJECTS THAT
// APPEAR IN THE GRAMMAR
/*********************/

class HandlerForCXXConstructAddExpr : public MatchFinder::MatchCallback {
public:
  HandlerForCXXConstructAddExpr() {}
  virtual void run(const MatchFinder::MatchResult &Result) {
    const auto *cxxConstructExpr =
        Result.Nodes.getNodeAs<clang::CXXConstructExpr>("VecAddConstructor");
    if (cxxConstructExpr != NULL) {
      // cxxConstructExpr->dump();
      // This is the entrance to the recursion call
      CXXMemberCallExprMatcher *matcher = new CXXMemberCallExprMatcher();
      matcher->match(cxxConstructExpr, Result.Context);
    } else {
      cout << "VecAddConstructor pointer is NULL" << endl;
    }
  }
};

class CXXConstructExprMatcher {
public:
  CXXConstructExprMatcher() {

    // literal
    CXXConstructExprMatcher_.addMatcher(cxxConstructExpr(argumentCountIs(3)).bind("VectorLitExpr"),
                                        &litHandler_);

    // member call
    StatementMatcher membercall =
        cxxConstructExpr(
            hasDescendant(cxxMemberCallExpr(hasDescendant(
                memberExpr(hasDeclaration(namedDecl(hasName("vec_add"))))))))
            .bind("VecAddConstructor");

    CXXConstructExprMatcher_.addMatcher(membercall, &addHandler_);
  }

  /*
(cxxConstructExpr (hasDescendant (cxxMemberCallExpr)), (hasDescendant
(memberExpr)), (hasDeclaration(namedDecl(hasName("add")))))
*/
  void match(const clang::CXXConstructExpr *consdecl, ASTContext *context) {
    CXXConstructExprMatcher_.match(*consdecl, *context);

    // cout<<"Inside CXXConstructExprMatcher, the top-level node is "<<
    // consdecl->getStmtClassName()<<endl; --works
  }

private:
  MatchFinder CXXConstructExprMatcher_;
  HandlerForCXXConstructLitExpr litHandler_;
  // HandlerForCXXMemberCallExpr cxxmembercallHandler_;
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
a corresponding expression in the domain, and that the
interpretation links this code/AST-node to that domain object.

Postcondition: the return value of this function is pointer to a new
object of type domain::Expr; that object is in the domain; it might
itself represent a complex expression tree; it links back to consdecl;
and the interpretation is updated to like consdecl to the new domain
object. This function works recursively to make sure that all of the
work of handling the top-level CXXConstructExpr is finished by the
time this function returns.

Explanation: This function works by first pattern matching on consdecl
any by then retrieving the results of that operation (side effects, I'm
afraid. The way in which this consdecl is turned into a domain object 
depends on the specific form of the expression being handled, but that
is the concern of the handler code invoked implicitly from here. As far
as this code is concerned, all it picks up is an expression. The cases 
handled by pattern matching include literal and add expressions.
- Vec v1(0.0,0.0,0.0) is a literal expression
- (v1.add(v2)).(v3.add(v4)) is an add expression (recursive)
*/
const domain::Expr *handleCXXConstructExpr(const clang::CXXConstructExpr *consdecl,
                                     ASTContext *context, SourceManager &sm) {
  cout << "Pattern matching Vector CXXConstructExpr at " << std::hex << consdecl << " and dispatching to handler.\n";
  CXXConstructExprMatcher *matcher = new CXXConstructExprMatcher();
  matcher->match(consdecl, context);
  /* 
     postcondition: as side effect of match,
     consdecl now has wrapper and interpretation.
  */
    if (!consdecl) {
        cerr << "handleCXXConstructExpr: match post failure, NULL consdecl.\n";
    }

    if (!interp_.code2coords_->expr_wrappers[consdecl]) {
        cerr << "handleCXXConstructExpr: match post failure, NULL wrapper.\n";
    }
  
  // Get code coordinates for given Clang AST node
   const coords::ExprASTNode *wrapper_key = interp_.code2coords_->expr_wrappers[consdecl];
  // Return domain object for code at these coordinates
  return interp_.coords2dom_->getExpressionInterp(wrapper_key);

  //cout << "Returning domain expression object (STUBBED OUT)\n";
  //return NULL; /* STUB */

  /*
  match consdecl with
  | literal <CXX three-argument pattern>, handle_literal(consdecl)
  | variable, handle_var
  | add expr, handle_add_expr

  StatementMatcher matchLit = ...;
  StatementMatcher matchVar = ...;
  Statement Matcher matchAdd = ...;

  handleXXXLit() {}
  handleCXXVar() {}
  HandleCXXAdd() { get left; get right part; handle_left; handle_right; glue
  them together }
  */
}

/*************************
 * Handle Vector DeclStmts
 *************************/

class VectorDeclStmtHandler : public MatchFinder::MatchCallback {
public:
  virtual void run(const MatchFinder::MatchResult &Result) {
    /*
    get DeclStatement from matcher
    get context
    get source manager
    get handle on variable declaration, vardecl
    be sure it has an initializer, then get the CXXConstructExpr initializer
    get handle on expression used to initialize the variable
    establish interpretation from consdecl to corresponding expression in the
    domain establish interpretation from variable in code to
    corresponding var object in domain finally establish interpretation
    linking overall declstmt in code to corresponding binding in domain
    */
    const auto *declstmt =
        Result.Nodes.getNodeAs<clang::DeclStmt>("VectorStatement");
    ASTContext *context = Result.Context;
    SourceManager &sm = context->getSourceManager();
    if (declstmt->isSingleDecl()) {

      const VarDecl *vardecl = dyn_cast<VarDecl>(declstmt->getSingleDecl());
      const clang::CXXConstructExpr *consdecl;
      if (vardecl->hasInit()) {
        consdecl =
            static_cast<const clang::CXXConstructExpr *>(vardecl->getInit());
      }
      // TODO: Fill in logic for error condition in preceding conditional
      cout << "Handling vector declaration statement\n";
      const domain::Expr *be = handleCXXConstructExpr(consdecl, context, sm);
      const domain::Identifier *bi =
          handleCXXConstructIdentifier(vardecl, context, sm);
      handleCXXConstructIdentifierBinding(declstmt, bi, be);
      cout << "Done handling vector declaration statement\n\n";
    } else {
      cout << "VectorDeclStmtHandler::run(): Something's wrong\n";
    }
  }
};

/********************************************
 * Top-level analyzer: Match Vector DeclStmts
 ********************************************/

class MyASTConsumer : public ASTConsumer {
public:
  MyASTConsumer() {
    StatementMatcher match_Vector_general_decl =
        declStmt(hasDescendant(varDecl(hasDescendant(
                     cxxConstructExpr(hasType(asString("class Vec")))))))
            .bind("VectorStatement");
    VectorDeclStmtMatcher.addMatcher(match_Vector_general_decl,
                                     &HandlerForVectorDeclStmt);
  }
  void HandleTranslationUnit(ASTContext &Context) override {
    VectorDeclStmtMatcher.matchAST(Context);
  }

private:
  MatchFinder VectorDeclStmtMatcher;
  VectorDeclStmtHandler HandlerForVectorDeclStmt;
};

/*******************************
 * Main Clang Tooling entry point
 ********************************/

class MyFrontendAction : public ASTFrontendAction {
public:
  MyFrontendAction() {}
  void EndSourceFileAction() override {
    bool consistent = interp_.domain_->isConsistent();
    cerr << (consistent ? "STUB: Good\n" : "STUB: Bad\n");
  }
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 StringRef file) override {
    return llvm::make_unique<MyASTConsumer>();
  }
};

/*****
 * Main
 ******/

int main(int argc, const char **argv) {
  CommonOptionsParser op(argc, argv, MyToolCategory);
  ClangTool Tool(op.getCompilations(), op.getSourcePathList());

  //InterpForm* interp = new InterpForm();
  interp_.domain_->addSpace("Space1");
  interp_.domain_->addSpace("Space2");

  return Tool.run(newFrontendActionFactory<MyFrontendAction>().get());

  //interp_.domain_ = new Domain();
  //interp_.coords2dom_ = new CoordsToDomain();
  //interp_.oracle_ = new Oracle(*interp_.domain_);
}