
#ifndef ROSVoid2Matcherguard
#define ROSVoid2Matcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSVoid2Matcher : public BaseMatcher {
public:
    ROSVoid2Matcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif