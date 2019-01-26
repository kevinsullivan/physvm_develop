#include <string>
#include <iostream>
#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
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
#include "Domain.h"
#include "Interpretation.h"
#include "Oracle.h"

using namespace clang;
using namespace clang::ast_matchers;
using namespace clang::driver;
using namespace clang::tooling;

using namespace std;
using namespace llvm;

/**************************************************
Fundamental data structure constructed by this tool
***************************************************/

/*
Sharing data via global variables is a bad idea, but we'll 
do it to get a working system. These variables are initialized 
in main() and updated during the parse tree traversal, as AST
node handlers are triggered. 
*/
Oracle         *oracle;
Domain         *domain;
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

/**********
 * HANDLERS
 *********/

// Vector class
class TypeVectorHandler : public MatchFinder::MatchCallback {
public:
  TypeVectorHandler() {}
  virtual void run(const MatchFinder::MatchResult &Result){
    const CXXRecordDecl *typeVector = 
      Result.Nodes.getNodeAs<clang::CXXRecordDecl>("TypeVectorDef");
    if(typeVector != NULL) {
      // NO ACTION
    }
  }
};

// Vector.add method
class VectorMethodAddHandler: public  MatchFinder::MatchCallback{
public:
  VectorMethodAddHandler () {}
  //  overrides run to take action when a match occurs
  virtual void run(const MatchFinder::MatchResult &Result) {
    // kevin's question is why would this ever be null? -- see clang details
    const CXXMethodDecl *vecAdd = 
      Result.Nodes.getNodeAs<clang::CXXMethodDecl>("VectorMethodAddDef");
    if(vecAdd != NULL) {
      // NO ACTION
    }
  }
};

// Vector instance declaration
class InstanceVecHandler:public MatchFinder::MatchCallback{
public:
  InstanceVecHandler()  {}
  virtual void run(const MatchFinder::MatchResult &Result){
    if(const auto *callstmt = 
      Result.Nodes.getNodeAs<clang::Stmt>("VecInstanceDecl")) {
      // ACTION:
      VectorASTNode& n = *new VectorASTNode(callstmt);
      Space& s = oracle->getSpaceForVector(n);
      Vector& abst_v = domain->addVector(s);
      interp->putVectorInterp(n, abst_v);
    }
  }
};

// Vector.add application
class OpAddHandler: public MatchFinder::MatchCallback{
public: 
  OpAddHandler () {}
  virtual void run(const MatchFinder::MatchResult &Result){
    if(const auto *dcstmt = 
      Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("VectorAddCall")) {
      // ACTION
      // Get a handle on arg #1
      // Get a handle on arg #2
      // Do some more stuff
      // ExprASTNode& exprn = *new ExprASTNode(dcstmt);
    }
  }
};


/*
 * ASTMatchers to find the code object of interests
 */

class MyASTConsumer : public ASTConsumer {
public:
  MyASTConsumer() {

    /**************
    Define Matchers
    ***************/

    DeclarationMatcher match_Vector_decl = 
      cxxRecordDecl(hasMethod(hasName("vec_add"))).bind("TypeVectorDefFoo");
    DeclarationMatcher match_Vector_add_decl = 
      cxxMethodDecl(hasName("vec_add")).bind("VectorMethodAddDef");
    StatementMatcher match_Vector_instance_decl = 
      declStmt(
        containsDeclaration(
          0, 
          varDecl(hasInitializer(cxxConstructExpr(argumentCountIs(3))))))
      .bind("VecInstanceDecl");
    StatementMatcher match_Vector_add_call =
      callExpr(callee(namedDecl(hasName("vec_add")))).bind("VectorAddCall");

    /* TODO: 
    - Match Vector class by name
    - Match Vector::vec_add only within class Vector
    - Match Vector instances by type
    - Match calls only to *Vector::* vec_add
    */

    /************
    Bind Handlers
    ************/

    Matcher.addMatcher(match_Vector_decl, &HandlerForVecDef);
    Matcher.addMatcher(match_Vector_add_decl, &HandlerForVecAddDef);
    Matcher.addMatcher(match_Vector_instance_decl, &HandlerForVecInstanceInit);
    Matcher.addMatcher(match_Vector_add_call, &HandlerForVecAdd);
  } 

  /******************
  * Grab AST Context
  ******************/

  virtual void Initialize(ASTContext& c) override { context_ = &c; }

  // called when ASTs for entire translation unit have been parsed
  void HandleTranslationUnit(ASTContext &Context) override {
    Matcher.matchAST(Context);
  }

private:
  ASTContext* context_;
  MatchFinder Matcher;
  TypeVectorHandler HandlerForVecDef;
  VectorMethodAddHandler HandlerForVecAddDef;
  InstanceVecHandler HandlerForVecInstanceInit;
  OpAddHandler HandlerForVecAdd;
};

/**************************************
Main entry point into Clang-based tool.
***************************************/ 

// For each source file provided to the tool, a new FrontendAction is created.


class MyFrontendAction : public ASTFrontendAction {
public:
  MyFrontendAction() {}
  void EndSourceFileAction() override {
    bool consistent = domain->isConsistent();
    cout << (consistent ? "Good\n" : "Bad\n");
  }

  std::unique_ptr<ASTConsumer> 
    CreateASTConsumer(CompilerInstance &CI, StringRef file) override 
  {
    return llvm::make_unique<MyASTConsumer>();
  }
};


/********
 * MAIN *
********/

int main(int argc, const char **argv) {
  // Initialize the code parsing infrastsructure
  CommonOptionsParser op(argc, argv, MyToolCategory);
  ClangTool Tool(op.getCompilations(), op.getSourcePathList());

  // Initialize domain, interpretation, and oracle
  domain = new Domain();
    Space& space1 = domain->addSpace("Space1");
    Space& space2 = domain->addSpace("Space2");
  interp = new Interpretation();
  oracle = new Oracle(*domain);

  // Analyze code and build interpretation
  return Tool.run(newFrontendActionFactory<MyFrontendAction>().get());
}
