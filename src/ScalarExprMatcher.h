/*
#ifndef bm
#define bm
#include "BaseMatcher.h"
#endif
*/

#ifndef scalarm
#define scalarm
#include "BaseMatcher.h"
#include "ScalarExprMatcher.h"
#include "Interpretation.h"

class ScalarExprMatcher : public BaseMatcher {
public:
    ScalarExprMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) {}
    virtual void search();
    virtual void run(const MatchFinder::MatchResult &Result);

};

#endif