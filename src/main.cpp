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
#include "Checker.h"

#include "MainMatcher.h"
//#include "ASTParse/VectorExprMatcher.h"

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
//#include <g3log/g3log.hpp>
//#include <g3log/logworker.hpp>

using namespace std;
using namespace llvm;
using namespace clang;
using namespace clang::ast_matchers;
using namespace clang::driver;
using namespace clang::tooling;


/*
Architectural decision: Main parser should deal in AST nodes only,
and call interpretation module to handle all other work. Do not use
coords, interp, domain objects.
*/

/***************************************
Data structure instantiated by this tool
****************************************/

interp::Interpretation* interp_;
clang::ASTContext *context_;
MainMatcher *programMatcher_;

// TODO: Decide whether we should pass context to interpretation.
// Answer is probably yes. Not currently being done.

// A vector literal is a constructor node applied to scalar args.
// There is no subordinate expression as there is when the value
// is given by an expression.
//
class HandlerForCXXConstructLitExpr : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    //LOG(DEBUG) <<"main::HandlerForCXXConstructLitExpr::run. Start.\n";
    const clang::CXXConstructExpr *lit_ast = 
      Result.Nodes.getNodeAs<clang::CXXConstructExpr>("VectorLitExpr");

    // TODO: Get actual coordinates from AST
    float x = 0;
    float y = 0;
    float z = 0;
    
    interp_->mkVector_Lit(lit_ast, x, y, z);
    //LOG(DEBUG) <<"main::HandlerForCXXConstructLitExpr::run. Done.\n";
  }
};

class HandlerForCXXConstructFloatLitExpr : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    //LOG(DEBUG) <<"main::HandlerForCXXConstructLitExpr::run. Start.\n";
    const clang::CXXConstructExpr *lit_ast = 
      Result.Nodes.getNodeAs<clang::CXXConstructExpr>("FloatLitExpr");

    // TODO: Get actual coordinates from AST
    float scalar = 0;
    
    interp_->mkFloat_Lit(lit_ast, scalar);
    //LOG(DEBUG) <<"main::HandlerForCXXConstructLitExpr::run. Done.\n";
  }
};

/*******************************
 * Handle Member Call Expression
 *******************************/

//Forward-reference handlers for member (left) and argument (expressions) of add application
void handle_member_expr_of_add_call(const clang::Expr *left);
void handle_arg0_of_add_call(const clang::Expr *right);

void handle_arg0_expr_of_mul_call(const clang::Expr *left);
void handle_arg1_expr_of_mul_call(const clang::Expr *right);

void handleMemberCallExpr(const CXXMemberCallExpr *ast)
{
  //LOG(DEBUG) <<"main::handleMemberCallExpr: Start, recurse on mem and arg\n";
  const clang::Expr *mem_ast = ast->getImplicitObjectArgument();
  const clang::Expr *arg_ast = ast->getArg(0);
  if (!mem_ast || !arg_ast) {
    //LOG(FATAL) <<"main::handleMemberCallExpr. Null pointer error.\n";
    return;
  }
  handle_member_expr_of_add_call(mem_ast);
  handle_arg0_of_add_call(arg_ast);
  interp_->mkVecVecAddExpr(ast, mem_ast, arg_ast);
  //LOG(DEBUG) <<"main::handleMemberCallExpr: Done.\n";
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
    //LOG(DEBUG) <<"main::HandlerForCXXMemberCallExprRight_DeclRefExpr: Start. DeclRefExpr = " << std::hex << declRefExpr_ast << "\n";
    interp_->mkVecVarExpr(declRefExpr_ast);
    //LOG(DEBUG) <<"main::HandlerForCXXMemberCallExprRight_DeclRefExpr: Done.\n";
  }
};

class HandlerForCXXMemberCallScalarExprRight_DeclRefExpr : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    const auto *declRefExpr_ast = Result.Nodes.getNodeAs<clang::DeclRefExpr>("DeclRefExpr");
    //LOG(DEBUG) <<"main::HandlerForCXXMemberCallExprRight_DeclRefExpr: Start. DeclRefExpr = " << std::hex << declRefExpr_ast << "\n";
    interp_->mkFloatVarExpr(declRefExpr_ast);
    //LOG(DEBUG) <<"main::HandlerForCXXMemberCallExprRight_DeclRefExpr: Done.\n";
  }
};

class HandlerForCXXConstructVecVarExpr : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    const CXXConstructExpr *ctor_ast = 
      Result.Nodes.getNodeAs<clang::CXXConstructExpr>("VecVarExpr4");
    const auto *declRefExpr_ast = Result.Nodes.getNodeAs<clang::DeclRefExpr>("VecVarExpr2");
    //LOG(DEBUG) <<"main::HandlerForCXXVecVarExpr: Start. VecVarExpr = " << std::hex << declRefExpr_ast << "\n";
    if(ctor_ast and declRefExpr_ast and !(ctor_ast->getNumArgs() == 3)){
      interp_->mkVecVarExpr(declRefExpr_ast);
      interp_->mkVector_Expr(ctor_ast, declRefExpr_ast); //????
    }
    //LOG(DEBUG) <<"main::HandlerForCXXVecVarExpr: Done.\n";
  }
};


class HandlerForCXXConstructFloatVarExpr : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    const CXXConstructExpr *ctor_ast = 
      Result.Nodes.getNodeAs<clang::CXXConstructExpr>("VecVarExpr4");
    const auto *declRefExpr_ast = Result.Nodes.getNodeAs<clang::DeclRefExpr>("VecVarExpr2");
    //LOG(DEBUG) <<"main::HandlerForCXXVecVarExpr: Start. VecVarExpr = " << std::hex << declRefExpr_ast << "\n";
    if(ctor_ast and declRefExpr_ast and !(ctor_ast->getNumArgs() == 1)){
      interp_->mkFloatVarExpr(declRefExpr_ast);
      interp_->mkFloat_Expr(ctor_ast, declRefExpr_ast); //????
    }
    //LOG(DEBUG) <<"main::HandlerForCXXVecVarExpr: Done.\n";
  }
};

// CXXMemberCallExpr is CXXMemberCallExprLeft + CXXMemberCallExprRight
class HandlerForCXXAddMemberCall : public MatchFinder::MatchCallback
{
public:
  //  Get left and right children of add expression and handle them by calls to other handlers
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    const CXXMemberCallExpr *memcall = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("MemberCallExpr");
    if (memcall == NULL)
    {
      //LOG(FATAL) <<"main::HandlerForCXXAddMemberCall::run: null memcall\n";
      return;
    }
    handleMemberCallExpr(memcall);
  }
};



// AddMemberParenExpr is: "(" some expression ")"
class HandlerForAddMemberParen : public MatchFinder::MatchCallback
{
public:
  //  Get left and right children of add expression and handle them by calls to other handlers
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    const ParenExpr *memparen = Result.Nodes.getNodeAs<clang::ParenExpr>("ParenExpr");
    if (memparen == NULL)
    {
      //LOG(FATAL) <<"main::HandlerForCXXAddMemberCall::run: null memcall\n";
      return;
    }
    const CXXMemberCallExpr *memcall = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("MemberCallExpr");
    if (memcall == NULL)
    {
      //LOG(FATAL) <<"main::HandlerForCXXAddMemberCall::ru`n: null memcall\n";
      return;
    }
    handleMemberCallExpr(memcall);
    interp_->mkVecParenExpr(memparen, memcall);
  }
};
/*
A Vector object constructed from a member expression
- Extract member expression on left, value expression on right
- Recursively handle each to give each an interpretation
- Finally give top-level node an interpretation
*/
class HandlerForCXXConstructAddExpr : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    const CXXConstructExpr *ctor_ast = 
      Result.Nodes.getNodeAs<clang::CXXConstructExpr>("VectorConstructAddExpr");
    if (ctor_ast == NULL)
    {
      //LOG(FATAL) <<"Error in HandlerForCXXConstructAddExpr::run. No constructor pointer\n";
      return;
    }
    //LOG(DEBUG) <<"main::HandlerForCXXConstructAddExpr: START. CXXConstructExpr is:\n";

    const CXXMemberCallExpr *vec_vec_add_member_call_ast =
        Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("MemberCallExpr");
    if (vec_vec_add_member_call_ast == NULL)
    {
      //LOG(FATAL) <<"Error in HandlerForCXXConstructAddExpr::run. No add expression pointer\n";
      return;
    }
    handleMemberCallExpr(vec_vec_add_member_call_ast);
    //LOG(DEBUG) <<"main::HandlerForCXXConstructAddExpr: Done.\n";
    interp_->mkVector_Expr(ctor_ast, vec_vec_add_member_call_ast);
  }
};

/*
In a member call, m.f(a), m is a member expression and a is an
argument expression. Each can take one of seeral forms. Each can
be either a variable expression or another call expression. Here
is where we do this case analysis. 
*/
class CXXMemberCallExprArg0Matcher
{
public:
  CXXMemberCallExprArg0Matcher()
  {
    // case: arg0 is a variable declaration reference expression
    // action: invoke dre_handler_::run as a match finder action
    const StatementMatcher DeclRefExprPattern = declRefExpr().bind("DeclRefExpr");
    CXXMemberCallExprArg0Matcher_.addMatcher(DeclRefExprPattern, &dre_handler_);
    //
    // case: arg0 is a cxx member call expression
    // action: invoke addHandler_::run as a match finder action
    const StatementMatcher CXXMemberCallExprPattern = cxxMemberCallExpr().bind("MemberCallExpr");
    CXXMemberCallExprArg0Matcher_.addMatcher(CXXMemberCallExprPattern, &mce_handler_);
  }
  void match(const clang::Expr &call_rhs)
  {
    //LOG(DEBUG) <<"CXXMemberCallExprArg0Matcher::match start\n";
    CXXMemberCallExprArg0Matcher_.match(call_rhs, *context_);
    //LOG(DEBUG) <<"CXXMemberCallExprArg0Matcher::match finish\n";
  }
private:
  MatchFinder CXXMemberCallExprArg0Matcher_;
  HandlerForCXXMemberCallExprRight_DeclRefExpr dre_handler_;
  HandlerForCXXAddMemberCall mce_handler_;
};


// Handle the single argument to an add application 
// TODO: Not handling all possible cases, e.g., literal
//
void handle_arg0_of_add_call(const clang::Expr *arg)
{
  //LOG(DEBUG) <<"domain::VecExpr *handle_arg0_of_add_call. START matcher for AST node:\n";
  CXXMemberCallExprArg0Matcher call_right_arg0_matcher; 
  call_right_arg0_matcher.match(*arg); 
  //LOG(DEBUG) <<"domain::VecExpr *handle_arg0_of_add_call. Done.\n";
}

/*
Member expression could be variable or function application
*/
class CXXMemberCallExprMemberExprMatcher
{
public:
  CXXMemberCallExprMemberExprMatcher()
  {
    // Member expression is a variable expression
    //
    const StatementMatcher DeclRefExprPattern = declRefExpr().bind("DeclRefExpr");
    CXXMemberCallExprMemberExprMatcher_.addMatcher(DeclRefExprPattern, &dre_handler_);

    // Member expression is a paren expression with some child expression inside
    //
    /* KEVIN: THE PROBLEM IS RIGHT HERE.
    This is an anti-pattern, in which we pass only the child node of a given AST node
    to be interpreted. The problem is that an invariant is violated, which is that after
    handling of the mem and arg ast nodes, the top-level mem node is no interpreted, but
    only the child member call expr node that we're handing off here to the handler. The
    solution, I think, will be for higher-level matching to strip the parens so that we
    never see a parenthesized expression at this level. INVARIANT: We must always create 
    an interpretation for the AST node we're given, not just for one of its children.
    */
    const StatementMatcher ParenCXXMemberCallExprPattern = 
      parenExpr(hasDescendant(cxxMemberCallExpr().bind("MemberCallExpr"))).bind("ParenExpr");
    CXXMemberCallExprMemberExprMatcher_.addMatcher(ParenCXXMemberCallExprPattern, &mpe_handler_);

    // Member expression a member call expression
    // TODO: We don't currently select for add calls, in particular, need to refine predicate
    //
    const StatementMatcher CXXMemberCallExprPattern = cxxMemberCallExpr().bind("MemberCallExpr");
    CXXMemberCallExprMemberExprMatcher_.addMatcher(CXXMemberCallExprPattern, &mce_handler_);
  }
  void match(const clang::Expr &call_rhs)
  {
    //LOG(DEBUG) <<"main::CXXMemberCallExprMemberExprMatcher. START matching. AST is:\n";
    CXXMemberCallExprMemberExprMatcher_.match(call_rhs, *context_);
    //LOG(DEBUG) <<"main::CXXMemberCallExprMemberExprMatcher. DONE matching.\n";
  }
private:
  MatchFinder CXXMemberCallExprMemberExprMatcher_;
  HandlerForCXXMemberCallExprRight_DeclRefExpr dre_handler_;
  HandlerForCXXAddMemberCall mce_handler_;
  HandlerForAddMemberParen mpe_handler_;
};

class CXXMemberCallExprMemberScalarExprMatcher
{
public:
  CXXMemberCallExprMemberScalarExprMatcher()
  {
    // Member expression is a variable expression
    //
    const StatementMatcher DeclRefExprPattern = declRefExpr().bind("DeclRefExpr");
    CXXMemberCallExprMemberExprMatcher_.addMatcher(DeclRefExprPattern, &dre_handler_);
  }
  void match(const clang::Expr &call_rhs)
  {
    //LOG(DEBUG) <<"main::CXXMemberCallExprMemberExprMatcher. START matching. AST is:\n";
    CXXMemberCallExprMemberExprMatcher_.match(call_rhs, *context_);
    //LOG(DEBUG) <<"main::CXXMemberCallExprMemberExprMatcher. DONE matching.\n";
  }
private:
  MatchFinder CXXMemberCallExprMemberExprMatcher_;
  HandlerForCXXMemberCallExprRight_DeclRefExpr dre_handler_;
};

/*
TODO: Inline? Looks like we can.
*/
void handle_member_expr_of_add_call(const clang::Expr *memexpr)
{
  //LOG(DEBUG) <<"main::handle_member_expr_of_add_call\n";
  if (memexpr == NULL)
  {
    //LOG(FATAL) <<"main::handle_member_expr_of_add_call: Error.Null argument\n";
  }
  CXXMemberCallExprMemberExprMatcher call_expr_mem_expr_matcher;
  call_expr_mem_expr_matcher.match(*memexpr);
  //LOG(DEBUG) <<"main::handle_member_expr_of_add_call. Done. \n";
 }





void handleBinaryCallExpr(const BinaryOperator *ast)
{
  //LOG(DEBUG) <<"main::handleMemberCallExpr: Start, recurse on mem and arg\n";
  const clang::Expr *vec_ast = ast->getLHS();
  const clang::Expr *flt_ast = ast->getRHS();
  if (!vec_ast || !flt_ast) {
    //LOG(FATAL) <<"main::handleMemberCallExpr. Null pointer error.\n";
    return;
  }
  //handle_member_expr_of_add_call(mem_ast);
  //handle_arg0_of_add_call(arg_ast);
  handle_arg0_expr_of_mul_call(vec_ast);
  handle_arg1_expr_of_mul_call(flt_ast);

  //-----
  //interp_->mkVecScalarMulExpr(ast, flt_ast, vec_ast);
  //LOG(DEBUG) <<"main::handleMemberCallExpr: Done.\n";
}


void handle_arg0_expr_of_mul_call(const clang::Expr *left){
  
  CXXMemberCallExprMemberExprMatcher call_expr_mem_expr_matcher;
  call_expr_mem_expr_matcher.match(*left);
}

void handle_arg1_expr_of_mul_call(const clang::Expr *right){
  //t
  CXXMemberCallExprMemberScalarExprMatcher call_expr_mem_expr_matcher;
  call_expr_mem_expr_matcher.match(*right);
}

class HandlerForCXXConstructMulExpr : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    const CXXConstructExpr *ctor_ast = 
      Result.Nodes.getNodeAs<clang::CXXConstructExpr>("VectorConstructMulExpr");
    if (ctor_ast == NULL)
    {
      //LOG(FATAL) <<"Error in HandlerForCXXConstructAddExpr::run. No constructor pointer\n";
      return;
    }
    //LOG(DEBUG) <<"main::HandlerForCXXConstructAddExpr: START. CXXConstructExpr is:\n";

    const BinaryOperator *vec_scalar_mul_member_call_ast =
        Result.Nodes.getNodeAs<clang::BinaryOperator>("BinaryCallExpr");
    if (vec_scalar_mul_member_call_ast == NULL)
    {
      //LOG(FATAL) <<"Error in HandlerForCXXConstructAddExpr::run. No add expression pointer\n";
      return;
    }
    handleBinaryCallExpr(vec_scalar_mul_member_call_ast);
    //LOG(DEBUG) <<"main::HandlerForCXXConstructAddExpr: Done.\n";
    interp_->mkVector_Expr(ctor_ast, vec_scalar_mul_member_call_ast);
  }
};

/*
A CXXConstructExpr is used to construct a vector object from
either a literal or from a vector expression. Here we do this
case analysis and dispatch accordingly.
*/
class CXXConstructExprMatcher
{
public:
  CXXConstructExprMatcher()
  {
    const StatementMatcher litMatcher = cxxConstructExpr(argumentCountIs(3))
      .bind("VectorLitExpr");
    CXXConstructExprMatcher_.addMatcher(litMatcher, &litHandler_);

    const StatementMatcher exprMatcher4 = cxxConstructExpr(hasDescendant(declRefExpr().bind("VecVarExpr2"))).bind("VecVarExpr4");
    CXXConstructExprMatcher_.addMatcher(exprMatcher4, &vecVarHandler_);

    const StatementMatcher addOpMatcher =
        cxxConstructExpr(hasDescendant(cxxMemberCallExpr(
                         hasDescendant(memberExpr(
                         hasDeclaration(namedDecl(hasName("vec_add"))))))
          .bind("MemberCallExpr")))
          .bind("VectorConstructAddExpr");
    CXXConstructExprMatcher_.addMatcher(addOpMatcher, &addHandler_);

    const StatementMatcher mulOpMatcher =
        cxxConstructExpr(hasDescendant(binaryOperator()
          .bind("BinaryCallExpr")))
          .bind("VectorConstructMulExpr");
    const StatementMatcher mulOpMatcher2 =
        cxxConstructExpr(hasDescendant(cxxMemberCallExpr(
                         hasDescendant(memberExpr(
                         hasDeclaration(namedDecl(hasName("operator*"))))))
          .bind("BinaryCallExpr")))
          .bind("VectorConstructMulExpr");
    CXXConstructExprMatcher_.addMatcher(mulOpMatcher, &mulHandler_);
    CXXConstructExprMatcher_.addMatcher(mulOpMatcher2, &mulHandler_);
  };
  void match(const clang::CXXConstructExpr *consdecl)
  {
    CXXConstructExprMatcher_.match(*consdecl, *context_);
  }
private:
  MatchFinder CXXConstructExprMatcher_;
  HandlerForCXXConstructLitExpr litHandler_;
  HandlerForCXXConstructAddExpr addHandler_;
  HandlerForCXXConstructMulExpr mulHandler_;
  HandlerForCXXConstructVecVarExpr vecVarHandler_;
};

class CXXConstructScalarExprMatcher
{
public:
  CXXConstructScalarExprMatcher()
  {
    const StatementMatcher litMatcher = cxxConstructExpr(argumentCountIs(1))
      .bind("ScalarLitExpr");
    CXXConstructExprMatcher_.addMatcher(litMatcher, &scalarLitHandler_);

    const StatementMatcher exprMatcher4 = cxxConstructExpr(hasDescendant(declRefExpr().bind("VecVarExpr2"))).bind("VecVarExpr4");
    CXXConstructExprMatcher_.addMatcher(exprMatcher4, &scalarVarHandler_);
    
  };
  void match(const clang::CXXConstructExpr *consdecl)
  {
    CXXConstructExprMatcher_.match(*consdecl, *context_);
  }
private:
  MatchFinder CXXConstructExprMatcher_;
  HandlerForCXXConstructFloatLitExpr scalarLitHandler_;
  HandlerForCXXConstructFloatVarExpr scalarVarHandler_;
};

/*
A vector declaration statement binds a vector-typed
identifier to a constructed vector object. This method
is invoked for each such declaration. It first builds
an interpretation for the identifier, then for the 
expression, and finally for the binding.
*/

class VectorDeclStmtHandler : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    const clang::DeclStmt *declstmt = Result.Nodes.getNodeAs<clang::DeclStmt>("VectorDeclStatement");
    const clang::CXXConstructExpr *consdecl = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("CXXConstructExpr");
    const clang::VarDecl *vardecl = Result.Nodes.getNodeAs<clang::VarDecl>("VarDecl");
    //LOG(DEBUG) <<"main::VectorDeclStmtHandler::run: START. AST (dump) is \n"; 
    interp_->mkVecIdent(vardecl);
    CXXConstructExprMatcher matcher;
    matcher.match(consdecl);
    interp_->mkVector_Def(declstmt, vardecl, consdecl);
    //LOG(DEBUG) <<"main::VectorDeclStmtHandler::run: Done.\n"; 
    }
};

class ScalarDeclStmtHandler : public MatchFinder::MatchCallback
{
public:
  virtual void run(const MatchFinder::MatchResult &Result)
  {
    const clang::DeclStmt *declstmt = Result.Nodes.getNodeAs<clang::DeclStmt>("ScalarDeclStatement");
    const clang::CXXConstructExpr *consdecl = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("CXXConstructExpr");
    const clang::VarDecl *vardecl = Result.Nodes.getNodeAs<clang::VarDecl>("VarDecl");
    //LOG(DEBUG) <<"main::VectorDeclStmtHandler::run: START. AST (dump) is \n"; 
    interp_->mkFloatIdent(vardecl);
    CXXConstructExprMatcher matcher;
    matcher.match(consdecl);
    interp_->mkFloat_Def(declstmt, vardecl, consdecl);
    //LOG(DEBUG) <<"main::VectorDeclStmtHandler::run: Done.\n"; 
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
    //StatementMatcher match_Vector_general_decl =to(cxxMethodDecl(hasName("=")))
    //    declStmt(hasDescendant(varDecl(hasDescendant(cxxConstructExpr(hasType(asString("class Vec"))).bind("CXXConstructExpr"))).bind("VarDecl"))).bind("VectorDeclStatement");
    StatementMatcher match_Scalar_general_decl =
      binaryOperator(allOf(hasLHS(anyOf(implicitCastExpr(expr()),binaryOperator())),hasRHS(anyOf(implicitCastExpr(expr()), binaryOperator())))).bind("ScalarDeclStatement");
      //cxxMemberCallExpr(has(memberExpr(member(hasName("vec_add")))));
      //cxxOperatorCallExpr(allOf(hasOverloadedOperatorName("="),has(declRefExpr(hasType(asString("class Vec"))))));
      //binaryOperator(allOf(hasOperatorName("="),has(declRefExpr(hasType(asString("float"))))));
      //cxxOperatorCallExpr(allOf(isAssignmentOperator(),has(declRefExpr(hasType(asString("class Vec"))))));
      //cxxOperatorCallExpr(allOf(hasType(asString("class Vec"),has(implicitCastExpr(has(declRefExpr()))))));
        //declStmt(has(varDecl(allOf(hasType(asString("float")),has(expr().bind("CXXConstructExpr")))))).bind("ScalarDeclStatement");
        /*
        CXXOperatorCallExpr 0x55e4e95e2c90 <line:80:3, col:11> 'Vec' lvalue
    | |-ImplicitCastExpr 0x55e4e95e2c78 <col:6> 'Vec &(*)(const Vec &) noexcept' <FunctionToPointerDecay>
    | | `-DeclRefExpr 0x55e4e95e28a8 <col:6> 'Vec &(const Vec &) noexcept' lvalue CXXMethod 0x55e4e95e26d0 'operator=' 

        */
      

    //DeclStmtMatcher.addMatcher(match_Vector_general_decl, &HandlerForVectorDeclStmt);
    //DeclStmtMatcher.addMatcher(match_Scalar_general_decl, &HandlerForScalarDeclStmt);
  }
  void HandleTranslationUnit(ASTContext &context) override
  {
    //DeclStmtMatcher.matchAST(context);
    programMatcher_->search();
    programMatcher_->start();
    
  }

private:
  MatchFinder ProgramFinder;
  VectorDeclStmtHandler HandlerForVectorDeclStmt;
  ScalarDeclStmtHandler HandlerForScalarDeclStmt;
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
    //LOG(DEBUG) <<"STUB Analysis result\n";
  }
  std::unique_ptr<ASTConsumer>
  CreateASTConsumer(CompilerInstance &CI, StringRef file) override
  {
    //LOG(INFO) << "Peirce. Building interpretation for " << file.str() << "." << std::endl;
    context_ = &CI.getASTContext();
    interp_->setASTContext(context_);
    programMatcher_ = new MainMatcher(context_, interp_);
    return llvm::make_unique<MyASTConsumer>(); 
  }
};

/*****
* Main
******/

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

  //using namespace g3;
  std::string logFile = "Peirce.log";
  std::string logDir = ".";
  //auto worker = LogWorker::createLogWorker();
  //auto defaultHandler = worker->addDefaultLogger(logFile, logDir);
  //g3::initializeLogging(worker.get());

  interp_ = new interp::Interpretation();   // default oracle
  
  //interp_->addSpace("_");
  interp_->addSpace("time");
  interp_->addSpace("geom");
  
  Tool.run(newFrontendActionFactory<MyFrontendAction>().get());
  //interp_->setAll_Spaces();
  interp_->mkVarTable();
  interp_->printVarTable();
  interp_->updateVarTable();


  cout <<"Spaces\n";
  cout <<interp_->toString_Spaces();
  cout <<"\nIdentifiers\n";
  cout <<interp_->toString_Idents(); 
  cout <<"\nExpressions\n";
  cout <<interp_->toString_Exprs();
  cout <<"\nVectors\n";
  cout <<interp_->toString_Vectors();
  cout <<"\nDefinitions\n"; 
  cout <<interp_->toString_Defs();
  cout << "\n";

  Checker *checker = new Checker(interp_);
  checker->Check();
}