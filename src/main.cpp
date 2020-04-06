#include <iostream>
#include <fstream>
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
  RewriteASTVisitor(ASTContext& ctxt) : RecursiveASTVisitor<RewriteASTVisitor>(), ctxt_{&ctxt} {}


  void AddConstraint(Stmt* stmt, VarDecl* decl)
  {
    if(stmt){
      auto fullLoc = this->ctxt_->getFullLoc(stmt->getSourceRange().getBegin());
      auto fullLocEnd = this->ctxt_->getFullLoc(stmt->getSourceRange().getEnd());
      auto newSourceLoc = this->ctxt_->getSourceManager().translateFileLineCol(fullLoc.getFileEntry(), fullLocEnd.getSpellingLineNumber() + 1, fullLoc.getSpellingColumnNumber());
      auto logStr = "\"Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: " + decl->getNameAsString() + ") with value : \" +  std::to_string(" + decl->getNameAsString() + ")";

      constraintWriter->InsertText(newSourceLoc, "\nLOG(INFO) << " + logStr + ");\n");
    }
    else{
      //log
    }
  }
  void AddConstraint(VarDecl* decl)
  {
    if(decl){
      auto declStmt = const_cast<Stmt*>(this->ctxt_->getParents(*decl)[0].get<Stmt>());
      AddConstraint(declStmt, decl);
    }
    else{
      //log
    }
  }

  void AddLoggingHeader(Stmt* stmt)
  {
    if(stmt){
      std::string initLogStr = "using namespace g3;";
      initLogStr +=  "auto worker = g3::LogWorker::createLogWorker();";
      initLogStr += "std::string logFile = \"Peirce.log\";std::string logDir = \".\";";
      initLogStr += "auto defaultHandler = worker->addDefaultLogger(logFile, logDir);";
      initLogStr += "g3::initializeLogging(worker.get());";
      auto fullLoc = this->ctxt_->getFullLoc(stmt->getSourceRange().getBegin());
      auto newSourceLoc = this->ctxt_->getSourceManager().translateFileLineCol(fullLoc.getFileEntry(), fullLoc.getSpellingLineNumber() + 1, fullLoc.getSpellingColumnNumber());
     
      constraintWriter->InsertText(newSourceLoc, "\n" + initLogStr +"\n");
      
    }
    else{
      //log
    }
  }

  void AddLoggingInclude(Decl* decl)
  {
      auto fullLoc = this->ctxt_->getFullLoc(decl->getSourceRange().getBegin());
      auto mf_id = this->ctxt_->getSourceManager().getMainFileID();
      auto newSourceLoc = this->ctxt_->getSourceManager().translateLineCol(mf_id, 1, 1);
     
      constraintWriter->InsertText(newSourceLoc, "\n#include <g3log/g3log.hpp>\n#include <g3log/logworker.hpp>\n");
      
  }

  bool VisitDecl(Decl* decl)
  {

    if(decl and isa<TranslationUnitDecl>(decl))
    {
      AddLoggingInclude(decl);
    }

    if(auto vd = dyn_cast<VarDecl>(decl))
    {

      bool needsConstraint = interp_->needsConstraint(vd);
      if(needsConstraint)
      {
        AddConstraint(vd);
      }
    }

    return true;
  }

  bool VisitStmt(Stmt* stmt)
  {


    if(stmt and isa<CompoundStmt>(stmt))
    {
      
      auto parentDecl = this->ctxt_->getParents(*stmt)[0].get<FunctionDecl>();

      if(parentDecl and parentDecl->isMain())
      {
        AddLoggingHeader(stmt);
      }
    }

    if(stmt and isa<DeclRefExpr>(stmt))
    {

      if(auto vd = dyn_cast<VarDecl>(dyn_cast<DeclRefExpr>(stmt)->getDecl()))
      {

        if(interp_->needsConstraint(vd))
        {
          auto parents = this->ctxt_->getParents(*stmt);
          Stmt* current = stmt;
          const CompoundStmt* cmpd = nullptr;
          while(!(cmpd = parents[0].get<CompoundStmt>())){
            current = const_cast<Stmt*>(parents[0].get<Stmt>());
            if(current){
              parents = this->ctxt_->getParents(*current);
            }
            else{
              parents = this->ctxt_->getParents(*const_cast<Decl*>(parents[0].get<Decl>()));
            }
          }
          AddConstraint(current, vd);
        }
      }
    }

    return true;
  }
private:
  ASTContext* ctxt_;

};


/**************************************
 * 
 * ***********************************/

bool rewriteMode = false;

class RewriteASTConsumer : public ASTConsumer
{
public:
  void HandleTranslationUnit(ASTContext &context) override 
  {
    RewriteASTVisitor visitor{context};
    visitor.TraverseDecl(context.getTranslationUnitDecl());

    auto mf_id = context.getSourceManager().getMainFileID();
    auto entry = context.getFullLoc(context.getSourceManager().getLocForStartOfFile(mf_id)).getFileEntry();



    auto *rewriter = constraintWriter->getRewriteBufferFor(mf_id);//returns null if no modification to source

    if(rewriter){
      //llvm::outs() << string(rewriter->begin(), rewriter->end());
      std::cout<<"Writing file..."<<entry->getName().str()<<std::endl;
      std::ofstream logcode;
      auto entryName = entry->getName().str();
      auto split = entryName.find_last_of('/');
      auto fname = entryName.substr(0, split+1) + "log_" + entryName.substr(split+1);
      logcode.open (fname, std::ofstream::out);
      logcode << string(rewriter->begin(), rewriter->end());
      logcode.close();
      std::cout<<"Done writing file "<<fname<<std::endl;

    }


  }
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
    if(!rewriteMode)
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

  auto toolAction = newFrontendActionFactory<MyFrontendAction>()  ;

  Tool.run(toolAction.get() );

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


//THE ORDER YOU RUN THE CHECKER AND THE REWRITE-PASS MATTERS. 
//Not only does Tool.run change/lose state on entry, but also on exit
 
  Checker *checker = new Checker(interp_);
  checker->Check();
  
  interp_->buildTypedDeclList();
  rewriteMode = true;
  Tool.run(toolAction.get());
  
}