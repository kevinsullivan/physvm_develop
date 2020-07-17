
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include <vector>
#include <iostream>

#include "MainMatcher.h"
#include "StatementProductionMatcher.h"
#include "TempROSMatcher.h"

#include "ASTToCoords.h"

/*

SCALAR_EXPR := (SCALAR_EXPR) | SCALAR_EXPR + SCALAR_EXPR | SCALAR_EXPR * SCALAR_EXPR | SCALAR_VAR | SCALAR_LITERAL

*/

using namespace clang::ast_matchers;

void MainMatcher::search(){
    //valid without pointers!
    DeclarationMatcher root =//isMain() <-- certain __important__ matchers like this are missing. find them.
        functionDecl(has(compoundStmt().bind("MainCompoundStatement")
        )).bind("MainCandidate");

    localFinder_.addMatcher(root, this);
};

void MainMatcher::run(const MatchFinder::MatchResult &Result){
    auto mainCompoundStatement = Result.Nodes.getNodeAs<clang::CompoundStmt>("MainCompoundStatement");
    auto mainCandidate = Result.Nodes.getNodeAs<clang::FunctionDecl>("MainCandidate");

    //since we can't check for main in clang, check each function candidate to see if it's main
    if(mainCandidate->isMain()){

        TempROSMatcher rootMatcher{this->context_, this->interp_};
        rootMatcher.search();

        std::vector<const clang::Stmt*> stmts;
        //visit each statement in the main procedure
        for(auto it = mainCompoundStatement->body_begin(); it != mainCompoundStatement->body_end();it++)
        {
        
            rootMatcher.visit(**it);
            auto h = *it;
            stmts.push_back(*it);
            if(auto dc = clang::dyn_cast<clang::DeclStmt>(h))
            {
                auto decl = dc->getSingleDecl();
                if(auto ddc = clang::dyn_cast<clang::VarDecl>(decl))
                {
                  //  ddc->getType()->dump();
                }
            }
        }

        this->interp_->mkCOMPOUND_STMT(mainCompoundStatement, stmts);

    }
};