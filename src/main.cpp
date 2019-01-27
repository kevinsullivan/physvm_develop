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
class VectorTypeDeclHandler : public MatchFinder::MatchCallback {
public:
  virtual void run(const MatchFinder::MatchResult &Result){
    const CXXRecordDecl *typeVector = 
      Result.Nodes.getNodeAs<clang::CXXRecordDecl>("VectorTypeDecl");
    if(typeVector != NULL) {
      // NO ACTION
    }
  }
};

// Vector.add method
class VectorAddMethodDeclHandler: public  MatchFinder::MatchCallback{
public:
  virtual void run(const MatchFinder::MatchResult &Result) {
    // kevin's question is why would this ever be null? -- see clang details
    const CXXMethodDecl *vecAdd = 
      Result.Nodes.getNodeAs<clang::CXXMethodDecl>("VectorAddMethodDecl");
    if(vecAdd != NULL) {
      // NO ACTION
    }
  }
};

// Vector instance declaration
class VectorInstanceDeclHandler:public MatchFinder::MatchCallback{
public:
  virtual void run(const MatchFinder::MatchResult &Result){
    if(const auto *vec_inst_decl = 
      Result.Nodes.getNodeAs<clang::Stmt>("VectorInstanceDecl")) {
      // ACTION:
      VectorASTNode& n = *new VectorASTNode(vec_inst_decl);
      ASTContext *con = Result.Context;
      SourceManager& sm = con->getSourceManager();  // not currently used
      FullSourceLoc FullLocation = 
        con->getFullLoc(vec_inst_decl->getBeginLoc());
      unsigned lineno = 0;
      unsigned colno = 0;
      if (FullLocation.isValid()) {
        lineno = FullLocation.getSpellingLineNumber(); // after postprocessing
        colno = FullLocation.getSpellingColumnNumber();
      }
      Space& s = oracle->getSpaceForVector("",lineno,colno); // fix: need filename
      Vector& abst_v = domain->addVector(s);
      interp->putVectorInterp(n, abst_v);
    }
  }
};

// Vector.add application
class VectorAddCallHandler: public MatchFinder::MatchCallback{
public: 
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


/*******************************************
 * AST Consumer: set up for and handle parse
 *******************************************/

class MyASTConsumer : public ASTConsumer {
public:
  MyASTConsumer() {

    /**************
    Define Matchers
    ***************/

    // Vector class declaration
    DeclarationMatcher match_Vector_decl = 
      cxxRecordDecl(hasMethod(hasName("vec_add"))).bind("TypeVectorDefFoo");

    // Vector::add method declaration
    DeclarationMatcher match_Vector_add_decl = 
      cxxMethodDecl(hasName("vec_add")).bind("VectorMethodAddDef");

    // Vector instance declaration
    StatementMatcher match_Vector_instance_decl = 
      declStmt(
        containsDeclaration(
          0, 
          varDecl(hasInitializer(cxxConstructExpr(argumentCountIs(3))))))
      .bind("VecInstanceDecl");

    // Vector::add call
    StatementMatcher match_Vector_add_call =
      callExpr(callee(namedDecl(hasName("vec_add")))).bind("VectorAddCall");

    /************
    Bind Handlers
    ************/

    Matcher.addMatcher(match_Vector_decl, &HandlerForVecDef);
    Matcher.addMatcher(match_Vector_add_decl, &HandlerForVecAddDef);
    Matcher.addMatcher(match_Vector_instance_decl, &HandlerForVecInstanceInit);
    Matcher.addMatcher(match_Vector_add_call, &HandlerForVecAdd);
  } 

  /******************************
  Main Entry Point to ASTConsumer
  ******************************/

  virtual void Initialize(ASTContext& c) override { context_ = &c; }
  void HandleTranslationUnit(ASTContext &Context) override {
    Matcher.matchAST(Context);
  }

private:
  ASTContext* context_;
  MatchFinder Matcher;
  VectorTypeDeclHandler HandlerForVecDef;
  VectorAddMethodDeclHandler HandlerForVecAddDef;
  VectorInstanceDeclHandler HandlerForVecInstanceInit;
  VectorAddCallHandler HandlerForVecAdd;
};

/**************************************
Main entry point into Clang-based tool.
***************************************/ 

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
  CommonOptionsParser op(argc, argv, MyToolCategory);
  ClangTool Tool(op.getCompilations(), op.getSourcePathList());

  domain = new Domain();
    domain->addSpace("Space1");
    domain->addSpace("Space2");
  interp = new Interpretation();
  oracle = new Oracle(*domain);

  return Tool.run(newFrontendActionFactory<MyFrontendAction>().get());
}