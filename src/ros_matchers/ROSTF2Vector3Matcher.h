
#ifndef ROSTF2Vector3Matcherguard
#define ROSTF2Vector3Matcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTF2Vector3Matcher : public BaseMatcher {
public:
    ROSTF2Vector3Matcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif