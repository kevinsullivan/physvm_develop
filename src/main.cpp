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
//#include "Checker.h"

#include "ros_matchers/ROSFunctionMatcher.h"
#include "ros_matchers/ROS1ProgramMatcher.h"
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

//#include <memory>
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
ROS1ProgramMatcher *programMatcher_;
Rewriter* constraintWriter;
bool rewriteMode;


/*
Architectural decision: Main parser should deal in AST nodes only,
and call interpretation module to handle all other work. Do not use
coords, interp, domain objects.
*/

/**************************************
 * NOTE: The next section of this file, ending with END LOGGING below can be 
 * skipped, if all you're interested in is Peirce functionality. This implements 
 * a prototype logging injection functionality to support future dynamic analysis
 * use cases.
 * 
 * This implments a portion of the "RecursiveASTVisitor" interface of Clang
 * It is used to recursively search an AST during the FrontendAction and determine where the program needs to add constraints.
 * This will get instantiated after the AST is initially parsed and types are added/inferred
 * Specifically, we're adding in constraints/logging code where we don't have any assigned type
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

      constraintWriter->InsertText(newSourceLoc, "\nLOG(INFO) << " + logStr + ";\n");
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

  //instantiate g3 in the main method
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

  //add a header to the top of the .cpp file to include all the necessary logging headers
  void AddLoggingInclude(Decl* decl)
  {
      auto mf_id = this->ctxt_->getSourceManager().getMainFileID();
      auto newSourceLoc = this->ctxt_->getSourceManager().translateLineCol(mf_id, 1, 1);
  
      constraintWriter->InsertText(newSourceLoc, "\n#include <g3log/g3log.hpp>\n#include <g3log/logworker.hpp>\n#include <string>\n");
      
  }

  //overridden callback from bass class (recursive AST visitor)
  //this method will trigger everytime the traversal hits a declaraction
  //we check if the decl needs a constraint, if so, insert it
  bool VisitDecl(Decl* decl)
  {

    if(decl and isa<TranslationUnitDecl>(decl))
    {
      AddLoggingInclude(decl);
    }

    if(auto vd = dyn_cast<VarDecl>(decl))
    {

      bool needsConstraint =false;// interp_->needsConstraint(vd);
      if(needsConstraint)
      {
        AddConstraint(vd);
      }
    }

    return true;
  }

  //another overridden callback
  //this will primarily check to see if the current AST node is a DeclRefExpr...if so, get it's corresponding declaraction
  //if that declaration needs a constraint, add some logging to the DeclRefExpr
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

        if(false)//interp_->needsConstraint(vd))
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
 * This will get initialized by the Frontend Action Tool IF the tool is set to "Rewrite Mode"
 * Rewrite mode should be set after the AST is parsed and types have been applied by the oracle and/or inferred
 * This is essentially the entry point for the RecursiveASTVisitor, which crawls through the AST and adds constraints.
 * ***********************************/

class RewriteASTConsumer : public ASTConsumer
{
public:
  void HandleTranslationUnit(ASTContext &context) override 
  {
    //this begins with a recursive traversal of the AST, 
    RewriteASTVisitor visitor{context};
    visitor.TraverseDecl(context.getTranslationUnitDecl());

    auto mf_id = context.getSourceManager().getMainFileID();
    auto entry = context.getFullLoc(context.getSourceManager().getLocForStartOfFile(mf_id)).getFileEntry();


    //clang will buffer all inserted text during the AST traversal.
    //this "rewrite buffer" will only exist if a constraint was added
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





/*
END LOGGING INSERTION CODE. 
*/





/***************************************
This will get instantiated by the Frontend Action Tool. It contains the entry point for the first pass through the program via the FrontendAction.
This will initiate a traversal of the AST which will build the virtual AST representation (Coords, Domain, Interp)
****************************************/

class MyASTConsumer : public ASTConsumer
{
public:
  MyASTConsumer(){}
  void HandleTranslationUnit(ASTContext &context) override
  {
    auto tud = context.getTranslationUnitDecl();
        auto& srcm = context.getSourceManager();
    for(auto d : tud->decls()){
            
            if(auto fn = clang::dyn_cast<clang::FunctionDecl>(d))
            {
                auto loc = fn->getLocation();

                auto srcloc = srcm.getFileLoc(loc);
                auto locstr = srcloc.printToString(srcm);
                //std::cout<<"HEY"<<locstr<<"\n";
            }
    }

    programMatcher_->setup();
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
      programMatcher_ = new ROS1ProgramMatcher(context_, interp_);
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

  const std::vector<std::string>& srcpaths = op.getSourcePathList();

  for(auto src: srcpaths){
    std::cout<<"SOURCE::"<<src<<"\n";
  }

  std::cout<<"SOURCE LENGTH::"<<srcpaths.size()<<"\n";

  ClangTool Tool(op.getCompilations(), srcpaths);

  //using namespace g3;
  std::string logFile = "Peirce.log";
  std::string logDir = ".";
  //auto worker = LogWorker::createLogWorker();
  //auto defaultHandler = worker->addDefaultLogger(logFile, logDir);
  //g3::initializeLogging(worker.get());

  interp_ = new interp::Interpretation();   // default oracle
  interp_->setSources(srcpaths);
  //interp_->addSpace("_");
  //interp_->addSpace("time");
  //interp_->addSpace("geom");
  //interp_->buildDefaultSpaces();


  //creates a "ToolAction" unique pointer object
  auto toolAction = newFrontendActionFactory<MyFrontendAction>()  ;

  // Parse the source and build empty interpretation
  Tool.run(toolAction.get() );

  /* 
  Iteratively obtain actual interpretation from user
  - maps the parsed AST into indices for printing and editing for the user
  - prints all variables that can be assigned
  - enters a while loop allowing user to select variables to edit or exit and perform inference
  */
  interp_->mkVarTable();
  interp_->printVarTable();
  interp_->updateVarTable();

//THE ORDER YOU RUN THE CHECKER AND THE REWRITE-PASS MATTERS. 
//Not only does Tool.run change/lose state on entry, but also on exit
 
 //this runs the lean type inference
  //Checker *checker = new Checker(interp_);
  //checker->Check();
  
  //Determines which variables can have a type assigned to them. If no type is assigned, we need to log/build constraints for these at runtime
  //interp_->buildTypedDeclList();
  //Re-run the tool, this time, build all the runtime constraints and logging.
  //rewriteMode = true;
  //Tool.run(toolAction.get());
  
}