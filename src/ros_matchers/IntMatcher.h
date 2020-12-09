
#ifndef IntMatcherguard
#define IntMatcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class IntMatcher : public BaseMatcher {
public:
    IntMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif