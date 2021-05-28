#pragma once
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "Interpretation.h"


#include <vector>

/*
This is the base class for all program AST parsing. It is modeled around a grammar with productions which may call 
other productions. All "Matcher" classes that inherit this should implement one of those productions. For example,
a vector a "Statement" production may have a "Vector Statement" case which should usually call a "Vector Expression" production

Every subclass must implement "void search()", which should register a set of clang matchers (StatementMatcher, for example)
which can pattern match on the Clang AST. When "void visit(const clang::Stmt &node)" is called on this object, it should
be after search is called, as visit checks an AST node to determine if any of the registered Matchers have a match within
the node.

This class also inherits from "clang::ast_matchers::MatchFinder::MatchCallback". Thus,
::run(const MatchFinder::MatchResult &Result) must be implemented by the child class. This method is triggered on an AST
match from "visit". It should check to see which "Match", among the registered "Matchers", triggered this method. Then,
it should handle the match. If it is a relevant object, we may want to store it using a relevant method from the "interp_"
property. 

We may want to recursively search its children by instantiating another production matcher, sub,
and passing the child AST Node to it. In that case, sub.search() and sub.visit(child node) should be called for the sub-production.
If it is a superfluous node, x, we don't want to track its state, however, we will want to tell x.parent to reference x.child
instead of x itself, as we don't want our backend to be aware of AST fluff. Thus, we will set our "childExprStore" property
to sub.getChildExprStore(). If the match was not superfluous, we will instead set childExprStore = matched_node_object, instead.
It is critical to set the childExprStore object so that a proper parse tree is built on the backend, however, it is not
necessary, for example, in the case of "statements", which generally are not being recursively called by a parent.

*/

using namespace clang::ast_matchers;

#ifndef bm
#define bm

class BaseMatcher : public MatchFinder::MatchCallback {
public:
    //requires: clang action state containing AST, program state containing virtual AST
    BaseMatcher(clang::ASTContext* context, interp::Interpretation* interp) : context_(context), interp_(interp) {}

    virtual void setup() = 0;
    virtual void run(const MatchFinder::MatchResult &Result) = 0;

    //Helper methods. See BaseMatcher.cpp. No need to override in subclass.
    virtual void start();
    virtual void visit(const clang::Stmt &node);

    clang::Stmt* getChildExprStore() const {
        //std::cout<<"GETTING CHILD EXPR STORE!!!\n";
        //this->childExprStore_->dump();
        //std::cout<<"DUMPING!\n";
        return this->childExprStore_;
    }
protected:
    MatchFinder localFinder_;//pattern matchers are stored here, matches are "named"
    clang::ASTContext* context_;
    interp::Interpretation* interp_;
    clang::Stmt* childExprStore_;

};

#endif