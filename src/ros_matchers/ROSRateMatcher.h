
#ifndef ROSRateMatcherguard
#define ROSRateMatcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSRateMatcher : public BaseMatcher {
public:
    ROSRateMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif