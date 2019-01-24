
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

#include "Code.h"
#include "Domain.h"
#include "Interpretation.h"
#include "Oracle.h"

using namespace clang;
using namespace clang::ast_matchers;
using namespace clang::driver;
using namespace clang::tooling;

using namespace std;

// consider removing this line, doesn't do anything for now to our knowledge
static llvm::cl::OptionCategory MatcherSampleCategory("Matcher Sample");

/*
Sharing data via global variables is a bad idea, but we'll do it here
to get a working system. These variables are initialized in main() and 
are then updated during the parse tree traversal, as handlers are triggered.
TODO: Use proper parameter passing rather than global variables here.
*/
Oracle         *oracle;
Domain         *domain;
Interpretation *interp;


/**********
 * HANDLERS
  declaration of Vector class
  declaration of Vector.add method
  declaration of Vector instance
  application of Vector.add 
 *********/


class TypeVectorHandler : public MatchFinder::MatchCallback{
public:
    TypeVectorHandler(Rewriter &Rewrite) : Rewrite(Rewrite) {}

  virtual void run(const MatchFinder::MatchResult &Result){
    if(const CXXRecordDecl *typeVector = Result.Nodes.getNodeAs<clang::CXXRecordDecl>("TypeVectorDef")){

      // ACTION: notice Vector class declaration but don't update the interp
      Rewrite.InsertText(typeVector->getBeginLoc(), "//Found Abstract Vector Type Definition\n",true, true);

    }
  }
private:
  Rewriter &Rewrite;
};


class VectorMethodAddHandler: public  MatchFinder::MatchCallback{
public:
  VectorMethodAddHandler (Rewriter &Rewrite) : Rewrite(Rewrite) {}

  //  overrides run to take action when a match occurs
  virtual void run(const MatchFinder::MatchResult &Result) {
    // kevin's question is why would this ever be null? -- see clang details
    const CXXMethodDecl *vecAdd = Result.Nodes.getNodeAs<clang::CXXMethodDecl>("VectorMethodAddDef");
    if(vecAdd != NULL) {

      // ACTION: Notice declaration of Vector.add; don't change interpreation
      Rewrite.InsertText(vecAdd->getBeginLoc(), "//Found Abstract Vector Add Definition\n",true, true);
    }
  }
private:
  Rewriter &Rewrite;
};


class InstanceVecHandler:public MatchFinder::MatchCallback{

public:
  InstanceVecHandler(Rewriter &Rewrite) : Rewrite(Rewrite) {}

  virtual void run(const MatchFinder::MatchResult &Result){
    if(const auto *callstmt = Result.Nodes.getNodeAs<clang::Stmt>("VecInstanceDecl")){

      // ACTION: notice vector instance, updated interpretation!
      Rewrite.InsertText(callstmt->getBeginLoc(), "//Found Vector Instance\n",true, true);

      // Get space with which to annotate vector instance
      // TODO: Need to connect n to the AST node we just found. How?
      // For now, just fake it, to get a system working.
      VectorASTNode& n = *new VectorASTNode();
      Space& s = oracle->getSpaceForVector(n);
      Vector& v = domain->addVector(s);
      interp->putVectorInterp(n, v);
    }
  }
private:
  Rewriter &Rewrite;
};


class OpAddHandler: public MatchFinder::MatchCallback{
public: 
  OpAddHandler (Rewriter &Rewrite) : Rewrite(Rewrite) {}
  virtual void run(const MatchFinder::MatchResult &Result){
    if(const auto *dcstmt = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("VectorAddCall")){
      // this code runs when an application of Vector.add is detected
      // Get a handle on arg #1
      // Get a handle on arg #2
      // Do some more sfuff
      Rewrite.InsertText(dcstmt->getBeginLoc(), "//Found Operation Add \n",true, true);
      // dcstmt->dump();
    }
  }
private:
  Rewriter &Rewrite;
};



/*
 * The ASTConsumer class contains ASTMatchers to find the list object of interests.
 */

class MyASTConsumer : public ASTConsumer {
public:
  MyASTConsumer(Rewriter &R) : HandlerForVecDef(R), HandlerForVecAddDef(R), 
              HandlerForVecInstanceInit(R), HandlerForVecAdd(R) {
    /*
    1. What exact queries are needed
    2. What precise forms of AST nodes get passed to handlers
    3. How do extract additional data when you get a match
    4. What do actually do when you get match?
    */

    // Finds Vector class definition
    // Can you match on the class by its name?
    Matcher.
      addMatcher(cxxRecordDecl(hasMethod(hasName("vec_add"))).bind("TypeVectorDef"),
                 &HandlerForVecDef);


    // Match definition of add method in Vector class
    // Can you narrow the scope of this search to Vector::vec_add?
    Matcher.addMatcher(cxxMethodDecl(
              hasName("vec_add")).bind("VectorMethodAddDef"), &HandlerForVecAddDef);

    // Match declaration of any instance of class Vector
    /*
     You really do have to narrow scope to match only declarations of objects
     of type Vector.
    */
    Matcher.addMatcher(declStmt(containsDeclaration(0, 
                  varDecl(hasInitializer(cxxConstructExpr
                    (argumentCountIs(3)))))).bind("VecInstanceDecl"),
                    &HandlerForVecInstanceInit);

    // Match on any application of add
    /*
      1. Need narrow scope to applications of Vector::vec_add
      2. Need to extract corresponding arguments as well ...
    */
    Matcher.addMatcher(callExpr(callee(namedDecl(
              hasName("vec_add")))).bind("VectorAddCall"),&HandlerForVecAdd);

  } 

  // not relevant at the moment, under development
  //
  void HandleTranslationUnit(ASTContext &Context) override {
    // Run the matchers when we have the whole TU parsed.
    Matcher.matchAST(Context);

  }

private:

  TypeVectorHandler HandlerForVecDef;
  VectorMethodAddHandler HandlerForVecAddDef;
  
  InstanceVecHandler HandlerForVecInstanceInit;
  OpAddHandler HandlerForVecAdd;

  MatchFinder Matcher;
};

// For each source file provided to the tool, a new FrontendAction is created.
class MyFrontendAction : public ASTFrontendAction {
public:
  MyFrontendAction() {}
  void EndSourceFileAction() override {
    TheRewriter.getEditBuffer(TheRewriter.getSourceMgr().getMainFileID())
        .write(llvm::outs());
  }

  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 StringRef file) override 
  {
    TheRewriter.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<MyASTConsumer>(TheRewriter);
  }

private:
  Rewriter TheRewriter;
};


/********
 * MAIN *
********/

int main(int argc, const char **argv) {
  // Initialize the code parsing infrastsructure
  CommonOptionsParser op(argc, argv, MatcherSampleCategory);
  ClangTool Tool(op.getCompilations(), op.getSourcePathList());

  // Initialize the domain, interpretation, and oracle modules
  domain = new Domain();
  interp = new Interpretation();
  oracle = new Oracle();

  // Analyze the code and build the interpretation
  return Tool.run(newFrontendActionFactory<MyFrontendAction>().get());
}


