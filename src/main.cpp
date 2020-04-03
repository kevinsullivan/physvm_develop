#include <iostream>
#include <string>

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Support/Casting.h"


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

interp::Interpretation* interp_;
clang::ASTContext *context_;
MainMatcher *programMatcher_;
Rewriter* constraintWriter;

/*
Architectural decision: Main parser should deal in AST nodes only,
and call interpretation module to handle all other work. Do not use
coords, interp, domain objects.
*/

/**************************************
 * 
 * ***********************************/

class RewriteASTVisitor : public RecursiveASTVisitor<RewriteASTVisitor>
{
public:
  void AddConstraint(Stmt* stmt)
  {
    constraintWriter->InsertText(stmt->getSourceRange().getBegin(), "/*Hello World!*/");
  }
  void AddConstraint(Decl* stmt)
  {
    constraintWriter->InsertText(stmt->getSourceRange().getBegin(), "/*Hello World!*/");
  }

  bool VisitDecl(Decl* decl)
  {
    if(isa<VarDecl>(decl))
    {
      auto vd = cast<VarDecl>(decl);
     // auto type = vd->getType().getAsString();
      if(interp_->needsConstraint(vd))
      {
        AddConstraint(decl);
      }
    }
  }

  bool VisitStmt(Stmt* stmt)
  {
    if(isa<DeclRefExpr>(stmt))
    {
      if(auto vd = dyn_cast<VarDecl>(dyn_cast<DeclRefExpr>(stmt)->getDecl()))
      {
        if(interp_->needsConstraint(vd))
        {
          AddConstraint(stmt);
        }
      }
    }
  }
};


/**************************************
 * 
 * ***********************************/

class RewriteASTConsumer : public ASTConsumer
{
public:
  void HandleTranslationUnit(ASTContext &context) override 
  {
    RewriteASTVisitor visitor;
    visitor.TraverseDecl(context.getTranslationUnitDecl());
  }
private:
  RewriteASTVisitor visitor;
};

/***************************************
Data structure instantiated by this tool
****************************************/

class MyASTConsumer : public ASTConsumer
{
public:
  MyASTConsumer(){}
  void HandleTranslationUnit(ASTContext &context) override
  {
    programMatcher_->search();
    programMatcher_->start();
  }
};

/*******************************
* Main Clang Tooling entry point
********************************/

class MyFrontendAction : public ASTFrontendAction
{
public:
  MyFrontendAction() : constraintWriterMode{false} {}
  void EndSourceFileAction() override
  {
    //bool consistent = interp_.isConsistent();
    //LOG(DEBUG) <<"STUB Analysis result\n";
  }
  std::unique_ptr<ASTConsumer>
  CreateASTConsumer(CompilerInstance &CI, StringRef file) override
  {
    //LOG(INFO) << "Peirce. Building interpretation for " << file.str() << "." << std::endl;
    if(!constraintWriterMode)
    {
      context_ = &CI.getASTContext();
      interp_->setASTContext(context_);
      programMatcher_ = new MainMatcher(context_, interp_);
      return llvm::make_unique<MyASTConsumer>(); 
    }
    else{
      constraintWriter = new Rewriter();
      constraintWriter->setSourceMgr(CI.getASTContext().getSourceManager(), CI.getLangOpts());
      return llvm::make_unique<RewriteASTConsumer>();
    }
  }

  void EnableConstraintWriter(){
    this->constraintWriterMode = true;
  }

private:
  bool constraintWriterMode;
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

  auto myAction = new MyFrontendAction();//unique_ptr<MyFrontendAction>{new MyFrontendAction()};
  
  tooling::runToolOnCode(myAction, argv[1]);

  //Tool.run(new FrontendActionFactory<MyFrontendAction>().get());
  //interp_->setAll_Spaces();
  interp_->mkVarTable();
  interp_->printVarTable();
  interp_->updateVarTable();


  cout <<"Spaces\n";
  cout <<interp_->toString_Spaces();
  cout <<"\nVector Identifiers\n";
  cout <<interp_->toString_Idents(); 
  cout <<"\nVector Expressions\n";
  cout <<interp_->toString_Exprs();
  cout <<"\nVectors\n";
  cout <<interp_->toString_Vectors();
  cout <<"\nVector Definitions\n"; 
  cout <<interp_->toString_Defs();
  cout << "\nVector Assignments\n";
  cout <<interp_->toString_Assigns();

  cout <<"Float Identifiers\n";
  cout <<interp_->toString_FloatIdents();
  cout <<"\nFloat Expressions\n";
  cout <<interp_->toString_FloatExprs();
  cout <<"\nFloats\n";
  cout <<interp_->toString_Floats();
  cout <<"\nFloat Definitions\n";
  cout <<interp_->toString_FloatDefs();
  cout << "\nFloat Assignments\n";
  cout <<interp_->toString_FloatAssigns();


  Checker *checker = new Checker(interp_);
  checker->Check();

  //get a list of variable declarations that have either been directly assigned a type, or have had a DeclRefExpr had a type assigned to them
  interp_->buildTypedDeclList();
  //go back through the AST
  myAction->EnableConstraintWriter();
  
  tooling::runToolOnCode(myAction, argv[1]);
}