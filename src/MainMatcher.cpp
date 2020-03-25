#pragma once

#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include <vector>
#include <iostream>

#include "MainMatcher.h"
#include "StatementProductionMatcher.h"

#include "ASTToCoords.h"

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

        StatementProductionMatcher rootMatcher{this->context_, this->interp_};
        rootMatcher.search();

        for(auto it = mainCompoundStatement->body_begin(); it != mainCompoundStatement->body_end();it++)
        {
            //std::cout<<"dumping node"<<std::endl;
            //(*it)->dump();
            //std::cout<<"dumped"<<std::endl;
            rootMatcher.visit(**it);
        }

    }
};