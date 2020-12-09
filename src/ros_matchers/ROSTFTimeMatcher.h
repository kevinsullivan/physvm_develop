
#ifndef ROSTFTimeMatcherguard
#define ROSTFTimeMatcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTFTimeMatcher : public BaseMatcher {
public:
    ROSTFTimeMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif