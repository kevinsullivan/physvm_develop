
#ifndef ROSTimeBaseMatcherguard
#define ROSTimeBaseMatcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTimeBaseMatcher : public BaseMatcher {
public:
    ROSTimeBaseMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif