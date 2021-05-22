
#ifndef ROSDurationMatcherguard
#define ROSDurationMatcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSDurationMatcher : public BaseMatcher {
public:
    ROSDurationMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif