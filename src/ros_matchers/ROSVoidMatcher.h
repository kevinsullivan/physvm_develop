
#ifndef ROSVoidMatcherguard
#define ROSVoidMatcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSVoidMatcher : public BaseMatcher {
public:
    ROSVoidMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif