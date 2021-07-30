
#ifndef ROSTimeMatcherguard
#define ROSTimeMatcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTimeMatcher : public BaseMatcher {
public:
    ROSTimeMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif