#include "BaseMatcher.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"


//Helper method implementation
//Begin traversal of AST. Can be initiated at any "production level".
//Currently using "MainMatcher.cpp", in other words, "Begin parsing AST at main method"
void BaseMatcher::start(){
    localFinder_.matchAST(*this->context_);
};

//Should be called after subclass method "search is called"
void BaseMatcher::visit(const  clang::Stmt &node){
    localFinder_.match(node, *(this->context_));
}