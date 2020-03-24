#pragma once
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "Interpretation.h"


#include <vector>

//add make unique to all matched node pointers

using namespace clang::ast_matchers;

#ifndef bm
#define bm

class BaseMatcher : public MatchFinder::MatchCallback {
public:
    BaseMatcher(clang::ASTContext* context, interp::Interpretation* interp) : context_(context), interp_(interp) {}

    virtual void search() = 0;
    virtual void run(const MatchFinder::MatchResult &Result) = 0;

    virtual void start();
    virtual void visit(const clang::Stmt &node);
protected:
    MatchFinder localFinder_;
    interp::Interpretation* interp_;
    clang::ASTContext* context_;

};

#endif