
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/AST/Decl.h"
#include <vector>
#include <iostream>

#include "ROS1ProgramMatcher.h"
#include "ROSStatementMatcher.h"

//#include "../ASTToCoords.h"

int TUDCount;

using namespace clang::ast_matchers;

void ROS1ProgramMatcher::setup(){
    //valid without pointers!
  /*  DeclarationMatcher root =//isMain() <-- certain __important__ matchers like this are missing. find them.
        functionDecl(has(compoundStmt().bind("MainCompoundStatement")
        )).bind("MainCandidate");
*/
    DeclarationMatcher roott =
        translationUnitDecl().bind("MainProg");

    //localFinder_.addMatcher(root, this);
    localFinder_.addMatcher(roott, this);
};

/*
This is a callback method that gets called when Clang matches on a pattern set up in the search method above.
*/
void ROS1ProgramMatcher::run(const MatchFinder::MatchResult &Result){
    //auto mainCompoundStatement = Result.Nodes.getNodeAs<clang::CompoundStmt>("MainCompoundStatement");
    //auto mainCandidate = Result.Nodes.getNodeAs<clang::FunctionDecl>("MainCandidate");

    auto tud = Result.Nodes.getNodeAs<clang::TranslationUnitDecl>("MainProg");

    auto srcs = this->interp_->getSources();
/*
    std::cout<<"Sources:\n";
    for(auto src:srcs)
    {
        std::cout<<src<<"\n";
    }*/

    if(tud){
        std::cout<<"TranslationUnitDeclCounter:"<<std::to_string(TUDCount++)<<"\n";
        if(TUDCount>1){
            std::cout<<"WARNING : UPDATE  LOGIC TO HANDLE MULTIPLE TRANSLATION UNITS.";
            throw "Bad Code!";
        }
    }
    std::vector<const clang::FunctionDecl*> globals;     
    if(tud)
    {
       //auto tud = clang::TranslationUnitDecl::castFromDeclContext(mainCandidate->getParent());
        auto& srcm = this->context_->getSourceManager();
        for(auto d : tud->decls()){
            
            if(auto fn = clang::dyn_cast<clang::FunctionDecl>(d))
            {
                auto loc = fn->getLocation();

                auto srcloc = srcm.getFileLoc(loc);
                auto locstr = srcloc.printToString(srcm);

                for(auto& src: srcs){
                    if(locstr.find(src) != string::npos){
                        std::vector<const clang::Stmt*> stmts;
                        if(auto cmpd = clang::dyn_cast<clang::CompoundStmt>(fn->getBody())){

                            for(auto it = cmpd->body_begin(); it != cmpd->body_end();it++)
                            {
                                ROSStatementMatcher rootMatcher{this->context_, this->interp_};
                                rootMatcher.setup();
                                //std::cout<<"dumping";
                                //(*it)->dump();
                                //std::cout<<"dumped";
                                rootMatcher.visit(**it);
                                if(rootMatcher.getChildExprStore()){
                                    //rootMatcher.getChildExprStore()->dump();
                                    stmts.push_back(rootMatcher.getChildExprStore());
                                }
                            }
                        
                            //this->interp_->mkCOMPOUND_STMT(cmpd, stmts);
                            this->interp_->buffer_operands(stmts);
                            this->interp_->mkNode("COMPOUND_STMT",cmpd,false);

                            if(fn->isMain())
                            {//s
                                //this->interp_->mkINT_FUNC_IDENT_STMT(fn, cmpd);

                                //this->interp_->mkMAIN_FUNC_DECL_STMT(fn, cmpd);
                                this->interp_->buffer_operand(cmpd);
                                this->interp_->mkNode("FUNC_MAIN",fn,false,true);
                            }
                            else{
                                //this->interp_->mkFUNCTION_STMT(fn, cmpd);
                            }

                            globals.push_back(fn);
                        
                        }
                        else{
                            std::cout<<"Warning : Unable to parse this node? \n";
                            fn->getBody()->dump();
                        }
                        
                    }
                }
            }
        }
        
        //this->interp_->mkSEQ_GLOBALSTMT(tud, globals);
        this->interp_->buffer_operands(globals);
        this->interp_->mkNode("COMPOUND_GLOBAL",tud,false,false);
    }
};