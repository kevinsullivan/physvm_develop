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
Oracle         *oracle;
// Domain         *domain;
Bridge         *bridge_domain;
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
      //cerr << "Found Vec class declaration\n";
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
      //cerr << "Found Vec::add method declaration\n";
    }
  }
};


/****************
 Vector::add call. CXXMemberCallExpr.

 Examples: 
 - v1.add(v2)              var add var    
 - (v1.add(v2)).add(v1)    expr add var
 - v1.add(v1.add(v2))      var add expr
 - foo().add(v2)           fun add var
 - foo().add(foo())        fun add fun
*****************/



class GeneralVectorHandler: public MatchFinder::MatchCallback{

public:
  virtual void run(const MatchFinder::MatchResult &Result){
    const auto *ptr_declstmt = Result.Nodes.getNodeAs<clang::DeclStmt>("VectorStatement");
    std::cout<<"\nFound the following declstmt:-----"<<endl;
    // ptr_declstmt->dump();

    // get identifier node 
    const VarDecl* identifier_VarDecl = dyn_cast<VarDecl>(ptr_declstmt->getSingleDecl());
    // get expression node 
    const clang::Expr *ptr_expression = identifier_VarDecl->getInit();

    // separately the cases of initialization and the assignment
    const clang::CXXConstructExpr *CCE_expression = static_cast<const clang::CXXConstructExpr *>(ptr_expression);

    // TODO design the matchers to do case analysis instead of hacking
    // This is not robust code
    const unsigned numArg = CCE_expression->getNumArgs();
    
    if (numArg > 1) 
      // initialization case
    {
      cout<<"initialization!"<<endl;
      // convert the identifier to Bridge identifier

      // Get file location information
      ASTContext *context = Result.Context;
      FullSourceLoc FullLocation = 
        context->getFullLoc(identifier_VarDecl->getBeginLoc());
      SourceManager& sm = context->getSourceManager();
      string where = FullLocation.printToString(sm);

      // HERE'S THE REAL ACTION
      Space& s = oracle->getSpaceForVector(where); // fix: need filename

      // Create code coordinate object to use in interp
      VectorASTNode& n = 
        *new VectorASTNode(ptr_declstmt, Result);

      // Create corresponding abstract vector in bridge_domain 
      const clang::Stmt* vecInstStmt = static_cast<const clang::Stmt*>(ptr_declstmt);
      VecVarExpr& abst_v = bridge_domain->addVecVarExpr(s,vecInstStmt);

      // Connect them through the interpretation
      interp->putVectorInterp(n, abst_v);

      // Construct Expression
      // iterate over the children of this node to get the literal values
      VecLitExpr& vle = bridge_domain-> addVecLitExpr(s);

      for(clang::Stmt::const_child_iterator it = CCE_expression->child_begin();
                      it!= CCE_expression->child_end(); ++ it)
      {
        double value = static_cast<const clang::FloatingLiteral*>(it->IgnoreImplicit())->getValueAsApproximateDouble();
        vle.addFloatLit(value);
      }
      // Add the binding
      bridge_domain->addLitExprBinding(abst_v,vle);
    }
    else
     // vec_add application
    {
      cout<<"vec_add application" <<endl; 
    }
    // recursively find the DeclRefExprs
    // bool VisitDeclRefExpr(DeclRefExpr* DRE) {
    //   const Decl* D = DRE->getDecl();
    //   cout<<"Found leave node!\n";
    //   return true; // returning false will abort the in-depth traversal.
    // } 
    // *add expression to the bridge_domain
    // constructExpression(ptr_expression);

    // *add identifier to bridge_domain
    

    // *create the binding 


  }
// private:
  // a class for visiting calls recursively 

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
    // DeclarationMatcher match_Vector_decl = cxxRecordDecl(hasName("Vec"))
    //   .bind("VectorTypeDecl");

    // Vector::add method declaration
    // DeclarationMatcher match_Vector_add_decl = 
    //   cxxMethodDecl(hasName("vec_add"))
    //     .bind("VectorAddMethodDecl");

    // OLD HANDLERS THAT HANDLES THE VECTOR CASES SEPARATELY
    // Vector instance declaration
    // DeclarationMatcher match_Vector_instance_decl = 
    //  varDecl(hasInitializer(cxxConstructExpr(hasType(cxxRecordDecl(hasName("Vec")))))).bind("VectorInstanceDecl");

    // Vector::add call
    // StatementMatcher match_Vector_add_call =
    //   cxxMemberCallExpr(hasDeclaration(namedDecl(hasName("vec_add"))))
    //     .bind("VecAddCall");

    // Add the new matcher that matches the Vector cases in general - instance and vec_ad application
    StatementMatcher match_Vector_general_decl = 
      declStmt(hasDescendant(varDecl(hasDescendant(cxxConstructExpr(hasType(asString("class Vec"))))))).bind("VectorStatement");

    /************
    Bind Handlers
    ************/

    // Matcher.addMatcher(match_Vector_decl, &HandlerForVecDef);
    // Matcher.addMatcher(match_Vector_add_decl, &HandlerForVecAddDef);
    
    // comment out those handlers that handles vectors cases separately 
    // Matcher.addMatcher(match_Vector_instance_decl, &HandlerForVecInstanceInit);
    // Matcher.addMatcher(match_Vector_add_call, &HandlerForVecAdd);

    Matcher.addMatcher(match_Vector_general_decl, &HandlerForVector);
    

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
  // New Handler class that handles the Vector cases in general,
  // including the instance and the vec_add application
  GeneralVectorHandler HandlerForVector;

  // VectorTypeDeclHandler HandlerForVecDef;
  // VectorAddMethodDeclHandler HandlerForVecAddDef;
  // VectorInstanceDeclHandler HandlerForVecInstanceInit;
  // VectorAddCallHandler HandlerForVecAdd;
};

/**************************************
Main entry point into Clang-based tool.
***************************************/ 

class MyFrontendAction : public ASTFrontendAction {
public:
  MyFrontendAction() {}
  void EndSourceFileAction() override {
    bool consistent = bridge_domain->isConsistent();
    cerr << (consistent ? "Good\n" : "Bad\n");
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

  bridge_domain = new Bridge();
    bridge_domain->addSpace("Space1");
    bridge_domain->addSpace("Space2");
  interp = new Interpretation();
  oracle = new Oracle(*bridge_domain);

  return Tool.run(newFrontendActionFactory<MyFrontendAction>().get());
}