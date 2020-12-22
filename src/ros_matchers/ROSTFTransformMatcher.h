
#ifndef ROSTFTransformMatcherguard
#define ROSTFTransformMatcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTFTransformMatcher : public BaseMatcher {
public:
    ROSTFTransformMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif