
#ifndef DoubleMatcherguard
#define DoubleMatcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class DoubleMatcher : public BaseMatcher {
public:
    DoubleMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif