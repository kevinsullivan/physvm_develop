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

#include "CodeCoords.h"
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
/*
  VectorTypeDeclHandler(ASTContext& c) : context_(c) : VectorTypeDeclHandler() {
      cout << "Setting Context in VectorTypeDeclHandler\n";
  }
*/
  virtual void run(const MatchFinder::MatchResult &Result) {
    cout << "Start VectorTypeDeclHandler\n";
    const CXXRecordDecl *typeVector = 
      Result.Nodes.getNodeAs<clang::CXXRecordDecl>("TypeVectorDef");
    if(typeVector != NULL) {
      // NO ACTION
    }
    cout << "End VectorTypeDeclHandler\n";
  }
};


// Vector.add method
class VectorAddMethodDeclHandler: public  MatchFinder::MatchCallback{
public:
/*
  VectorAddMethodDeclHandler(ASTContext& c) : context_(c) {
      cout << "Setting Context in VectorAddMethodDeclHandler\n";
  }
*/
  virtual void run(const MatchFinder::MatchResult &Result) {
    cout << "Start VectorAddMethodDeclHandler\n";    
    // kevin's question is why would this ever be null? -- see clang details
    const CXXMethodDecl *vecAdd = 
      Result.Nodes.getNodeAs<clang::CXXMethodDecl>("VectorMethodAddDef");
    if(vecAdd != NULL) {
      // NO ACTION
    }
    cout << "End VectorAddMethodDeclHandler\n";
  }
};

// Vector instance declaration
class VectorInstanceDeclHandler:public MatchFinder::MatchCallback{
public:
/*
  VectorInstanceDeclHandler(ASTContext& c) : context_(c) {
      cout << "Setting Context in VectorInstanceDeclHandler\n";
  }
*/
  virtual void run(const MatchFinder::MatchResult &Result) {
    cout << "Start VectorInstanceDeclHandler\n";
    if(const auto *callstmt = 
      Result.Nodes.getNodeAs<clang::DeclStmt>("VecInstanceDecl")) {
      // ACTION:
      //SourceLocation loc = callstmt->getBeginLoc();
      //FullSourceLoc fullloc = context_->getFullLoc(loc);
      callstmt->dump();
      VectorASTNode& n = *new VectorASTNode(callstmt);
      Space& s = oracle->getSpaceForVector("",0,0);
      Vector& abst_v = domain->addVector(s);
      interp->putVectorInterp(n, abst_v);
    }
    cout << "End VectorInstanceDeclHandler\n";
  }
};

// Vector.add application
class VectorAddCallHandler: public MatchFinder::MatchCallback{
public: 
  virtual void run(const MatchFinder::MatchResult &Result) {
    cout << "Start VectorAddCallHandler\n";
    if(const auto *dcstmt = 
      Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("VectorAddCall")) {
      // ACTION
      // Get a handle on arg #1
      // Get a handle on arg #2
      // Do some more stuff
      // ExprASTNode& exprn = *new ExprASTNode(dcstmt);
    }
    cout << "End VectorAddCallHandler\n";
  }
};


/*******************************************
 * AST Consumer: set up for and handle parse
 *******************************************/

class MyASTConsumer : public ASTConsumer {
public:
  MyASTConsumer() {

    cout << " Defining matchers\n";

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

   cout << "Binding handlers\n";

    Matcher.addMatcher(match_Vector_decl, HandlerForVecDef);
    Matcher.addMatcher(match_Vector_add_decl, HandlerForVecAddDef);
    Matcher.addMatcher(match_Vector_instance_decl, HandlerForVecInstanceInit);
    Matcher.addMatcher(match_Vector_add_call, HandlerForVecAdd);
  } 

  /******************
  * Grab AST Context
  ******************/

  virtual void Initialize(ASTContext& c) override { 
    cout << "Initializing AST Consumer with Context = " << &c << "\n";
    context_ = &c; 
    HandlerForVecDef = new VectorTypeDeclHandler();
    HandlerForVecAddDef = new VectorAddMethodDeclHandler();
    HandlerForVecInstanceInit = new VectorInstanceDeclHandler();
    HandlerForVecAdd = new VectorAddCallHandler();
    cout << "Done Initializing AST Consumer\n";
  }


  /*
  * 
  */ 
  void HandleTranslationUnit(ASTContext &Context) override {
    cout << "Start HandleTranslation Unit\n";
    cout << "this = " << this << "\n";
    cout << "Context = " << &Context << "\n";
    cout << " Matcher = " << &Matcher << "\n";
    cout << "HandlerForVecDef = " << HandlerForVecDef << "\n";
    cout << "HandlerForVecAddDef = " << HandlerForVecAddDef << "\n";
    cout << "HandlerForVecInstanceInit = " << HandlerForVecInstanceInit << "\n";
    cout << "HandlerForVecAdd = " << HandlerForVecAdd << "\n";
    Matcher.matchAST(Context);
    cout << "End HandleTranslation Unit\n";
  }

private:
  ASTContext* context_;
  MatchFinder Matcher;
  VectorTypeDeclHandler* HandlerForVecDef;
  VectorAddMethodDeclHandler* HandlerForVecAddDef;
  VectorInstanceDeclHandler* HandlerForVecInstanceInit;
  VectorAddCallHandler* HandlerForVecAdd;
};

/**************************************
Main entry point into Clang-based tool.
***************************************/ 

class MyFrontendAction : public ASTFrontendAction {
public:
  MyFrontendAction() {}

  // return an one of our ASTConsumers per translation unit
  virtual std::unique_ptr<ASTConsumer> CreateASTConsumer(
    CompilerInstance &CI, StringRef file) override 
  {
    return llvm::make_unique<MyASTConsumer>();
  }

  void EndSourceFileAction() override {
    cout << "Start EndSourceFileAction\n";
    bool consistent = domain->isConsistent();
    cout << (consistent ? "Good\n" : "Bad\n");
    cout << "End EndSourceFileAction\n";
  }
};

/********
 * MAIN *
********/

int main(int argc, const char **argv) {

  // Initialize the code parsing infrastsructure
  cout << "Initializing compiler\n";
  CommonOptionsParser op(argc, argv, MyToolCategory);
  ClangTool Tool(op.getCompilations(), op.getSourcePathList());

  // Initialize domain, interpretation, and oracle
  cout << "Initializing interpretation\n"; 
  domain = new Domain();
    domain->addSpace("S1");
    domain->addSpace("S2");
  interp = new Interpretation();
  oracle = new Oracle(*domain);

  // Analyze code and build interpretation
  cout << "Start running tool\n";
  return Tool.run(newFrontendActionFactory<MyFrontendAction>().get());
  cout << "Finish running tool\n";
}
