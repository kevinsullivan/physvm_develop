
#ifndef ROSBooleanMatcherguard
#define ROSBooleanMatcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSBooleanMatcher : public BaseMatcher {
public:
    ROSBooleanMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif