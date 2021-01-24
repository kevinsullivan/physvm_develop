
#ifndef ROSTFQuaternionMatcherguard
#define ROSTFQuaternionMatcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTFQuaternionMatcher : public BaseMatcher {
public:
    ROSTFQuaternionMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif