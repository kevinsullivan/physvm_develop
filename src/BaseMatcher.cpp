#include "BaseMatcher.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"



void BaseMatcher::start(){
    localFinder_.matchAST(*this->context_);
};
void BaseMatcher::visit(const  clang::Stmt &node){
    localFinder_.match(node, *(this->context_));
}