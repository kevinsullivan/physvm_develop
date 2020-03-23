

#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include <vector>


#include "MainMatcher.h"
#include "StatementProductionMatcher.h"

/*

SCALAR_EXPR := (SCALAR_EXPR) | SCALAR_EXPR + SCALAR_EXPR | SCALAR_EXPR * SCALAR_EXPR | SCALAR_VAR | SCALAR_LITERAL

*/

using namespace clang::ast_matchers;

void MainMatcher::search(){
    //nice and valid without pointers!
    DeclarationMatcher root =//isMain() <-- certain __important__ matchers like this are missing. find them.
        functionDecl(has(compoundStmt().bind("MainCompoundStatement")
        )).bind("MainCandidate");

    localFinder_.addMatcher(root, this);
};

void MainMatcher::run(const MatchFinder::MatchResult &Result){
    auto mainCompoundStatement = Result.Nodes.getNodeAs<clang::CompoundStmt>("MainCompoundStatement");
    auto mainCandidate = Result.Nodes.getNodeAs<clang::FunctionDecl>("MainCandidate");


    if(mainCandidate->isMain()){
        //mainCandidate->dump();
        //mainCompoundStatement->dump();

        StatementProductionMatcher rootMatcher{this->context_};
        rootMatcher.search();
        //mainCompoundStatement->dump();
        (*(mainCompoundStatement->body_front())).dump();
        rootMatcher.visit(*(mainCompoundStatement->body_front()));

        for(auto it = mainCompoundStatement->body_begin(); it++; it != mainCompoundStatement->body_end())
        {
            (*it)->dump();
            rootMatcher.visit(**it);
        }

       // rootMatcher.visit(*mainCompoundStatement);
    }
};