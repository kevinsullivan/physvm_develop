
#ifndef ROSTF2DurationMatcherguard
#define ROSTF2DurationMatcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTF2DurationMatcher : public BaseMatcher {
public:
    ROSTF2DurationMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif