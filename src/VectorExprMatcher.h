

#ifndef vectorm
#define vectorm
#include "BaseMatcher.h"
#include "Interpretation.h"

class VectorExprMatcher : public BaseMatcher {
public:
    VectorExprMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) {}
    virtual void search();
    virtual void run(const MatchFinder::MatchResult &Result);

};

#endif