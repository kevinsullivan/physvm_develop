
#ifndef VoidMatcherguard
#define VoidMatcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class VoidMatcher : public BaseMatcher {
public:
    VoidMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif