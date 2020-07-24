#ifndef rosm
#define rosm
#include "BaseMatcher.h"
#include "Interpretation.h"


class TempROSMatcher : public BaseMatcher {
public:
    TempROSMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) {}
    virtual void search();
    virtual void run(const MatchFinder::MatchResult &Result);

};

#endif