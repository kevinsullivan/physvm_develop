
#ifndef ROSDurationBaseMatcherguard
#define ROSDurationBaseMatcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSDurationBaseMatcher : public BaseMatcher {
public:
    ROSDurationBaseMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif