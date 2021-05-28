
#ifndef FloatMatcherguard
#define FloatMatcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class FloatMatcher : public BaseMatcher {
public:
    FloatMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif