
#ifndef ROSVoid1Matcherguard
#define ROSVoid1Matcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSVoid1Matcher : public BaseMatcher {
public:
    ROSVoid1Matcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif