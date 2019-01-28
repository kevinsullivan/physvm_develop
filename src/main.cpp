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

/*
 Vector class
*/
class VectorTypeDeclHandler : public MatchFinder::MatchCallback {
public:
  virtual void run(const MatchFinder::MatchResult &Result){
    const CXXRecordDecl *typeVector = 
      Result.Nodes.getNodeAs<clang::CXXRecordDecl>("VectorTypeDecl");
    if(typeVector != NULL) {
      // NO ACTION
      //cout << "Found Vec class declaration\n";
    }
  }
};

/*
 Vector.add method
*/
class VectorAddMethodDeclHandler: public  MatchFinder::MatchCallback{
public:
  virtual void run(const MatchFinder::MatchResult &Result) {
    // kevin's question is why would this ever be null? -- see clang details
    const CXXMethodDecl *vecAdd = 
      Result.Nodes.getNodeAs<clang::CXXMethodDecl>("VectorAddMethodDecl");
    if(vecAdd != NULL) {
      // NO ACTION
      //cout << "Found Vec::add method declaration\n";
    }
  }
};

/*
 Vector instance declaration
*/
class VectorInstanceDeclHandler:public MatchFinder::MatchCallback{
public:
  virtual void run(const MatchFinder::MatchResult &Result){
    if(const auto *vec_inst_decl = 
      Result.Nodes.getNodeAs<clang::VarDecl>("VectorInstanceDecl")) {
      // ACTION:
      //cout << "Found Vec instance declaration\n";

      // Get file location information
      ASTContext *context = Result.Context;
      FullSourceLoc FullLocation = 
        context->getFullLoc(vec_inst_decl->getBeginLoc());
      SourceManager& sm = context->getSourceManager();
      string where = FullLocation.printToString(sm);

      // HERE'S THE REAL ACTION
      Space& s = oracle->getSpaceForVector(where); // fix: need filename

      // Create code coordinate object to use in interp
      VectorASTNode& n = 
        *new VectorASTNode(vec_inst_decl, Result);

      // Create corresponding abstract vector in domain 
      Vector& abst_v = domain->addVector(s);

      // Connect them through the interpretation
      interp->putVectorInterp(n, abst_v);
    }
  }
};

/*
 Vector::add call
*/
class VectorAddCallHandler: public MatchFinder::MatchCallback{
public: 
  virtual void run(const MatchFinder::MatchResult &Result){
    //cout << "VectorAddCallHandler called -- checking node\n";
    const auto *exp = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("VecAddCall");
    if(exp != NULL) {
      // ACTION

      // Fields accessible from exp: CURRENTLY UNUSED
      const Expr* const implicitArg =	exp->getImplicitObjectArgument();
      const CXXMethodDecl* const methodDecl =	exp->getMethodDecl();
      const CXXRecordDecl* const recordDecl = exp-> getRecordDecl(); 
      unsigned numArgs= exp->getNumArgs();
      const Expr* const* args = exp->getArgs();

      // Get file location information of exp
      ASTContext* context = Result.Context;
      FullSourceLoc FullLocation = 
        context->getFullLoc(exp->getBeginLoc());
      SourceManager& sm = context->getSourceManager();
      string where = FullLocation.printToString(sm);

      // Create code coordinate object to use in interp
      ExprASTNode& n = 
        *new ExprASTNode(exp, Result);

      // STUBBED OUT: Create domain expression and add interp
      // Get coord coordinates for arguments
      // These are not the right sub-exprs!
      // This is not the right space!
      Space& s = domain->addSpace("STUB Space for Expr");
      Vector& v1 = domain->addVector(s);
      Vector& v2 = domain->addVector(s);

      // Create the expression object
      Expression& abst_e = domain->addExpression(v1,v2);

      // Connect code to abstraction through interpretation
      interp->putExpressionInterp(n, abst_e);

      cout<<"Found operation application at "<< where <<endl;
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
    Define MATCHERS
    ***************/

    // Vector class declaration
    DeclarationMatcher match_Vector_decl = recordDecl(hasName("Vec"))
      .bind("VectorTypeDecl");

    // Vector::add method declaration
    DeclarationMatcher match_Vector_add_decl = 
      cxxMethodDecl(hasName("vec_add"))
        .bind("VectorAddMethodDecl");

    // Vector instance declaration
    DeclarationMatcher match_Vector_instance_decl = 
     varDecl(hasInitializer(cxxConstructExpr(hasType(cxxRecordDecl(hasName("Vec"))))))
        .bind("VectorInstanceDecl");

    // Vector::add call
    StatementMatcher match_Vector_add_call =
      cxxMemberCallExpr(hasDeclaration(namedDecl(hasName("vec_add"))))
        .bind("VecAddCall");
    
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
    CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
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