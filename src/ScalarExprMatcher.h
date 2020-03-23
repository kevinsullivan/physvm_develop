/*
#ifndef bm
#define bm
#include "BaseMatcher.h"
#endif
*/
#include "BaseMatcher.h"

#ifndef scalarm
#define scalarm

class ScalarExprMatcher : public BaseMatcher {
public:
    ScalarExprMatcher(clang::ASTContext* context) : BaseMatcher(context) {}
    virtual void search();
    virtual void run(const MatchFinder::MatchResult &Result);

};

#endif