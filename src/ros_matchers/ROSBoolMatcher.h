
#ifndef ROSBoolMatcherguard
#define ROSBoolMatcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSBoolMatcher : public BaseMatcher {
public:
    ROSBoolMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif