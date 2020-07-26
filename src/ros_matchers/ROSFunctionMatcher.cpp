
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/AST/Decl.h"
#include <vector>
#include <iostream>

#include "ROSFunctionMatcher.h"
#include "ROSStatementMatcher.h"

#include "../ASTToCoords.h"

/*

SCALAR_EXPR := (SCALAR_EXPR) | SCALAR_EXPR + SCALAR_EXPR | SCALAR_EXPR * SCALAR_EXPR | SCALAR_VAR | SCALAR_LITERAL

*/

using namespace clang::ast_matchers;

void ROSFunctionMatcher::search(){
    //valid without pointers!
    DeclarationMatcher root =//isMain() <-- certain __important__ matchers like this are missing. find them.
        functionDecl(has(compoundStmt().bind("MainCompoundStatement")
        )).bind("MainCandidate");

    localFinder_.addMatcher(root, this);
};

/*
This is a callback method that gets called when Clang matches on a pattern set up in the search method above.
*/
void ROSFunctionMatcher::run(const MatchFinder::MatchResult &Result){
    auto mainCompoundStatement = Result.Nodes.getNodeAs<clang::CompoundStmt>("MainCompoundStatement");
    auto mainCandidate = Result.Nodes.getNodeAs<clang::FunctionDecl>("MainCandidate");

    //since we can't check for main in clang, check each function candidate to see if it's main
    if(mainCandidate->isMain()){

        // stmts gets converted into a SEQ construct in lang.
        std::vector<const clang::Stmt*> stmts;

        //visit each statement in the main procedure
        for(auto it = mainCompoundStatement->body_begin(); it != mainCompoundStatement->body_end();it++)
        {
            ROSStatementMatcher rootMatcher{this->context_, this->interp_};
            rootMatcher.search();
            rootMatcher.visit(**it);
            auto h = *it;

            if(rootMatcher.getChildExprStore()){
                stmts.push_back(rootMatcher.getChildExprStore());
            }
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
        //this->interp_->mkMAIN_STMT(mainCandidate, mainCompoundStatement);
        //auto tud = clang::TranslationUnitDecl::castFromDeclContext(mainCandidate->getParent());
        //std::vector<const clang::FunctionDecl*> globals;
        //globals.push_back(mainCandidate);
        //this->interp_->mkSEQ_GLOBALSTMT(tud, globals);
    }
};