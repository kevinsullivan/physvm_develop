
#ifndef ROSTF2Transformguard
#define ROSTF2Transformguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTF2Transform : public BaseMatcher {
public:
    ROSTF2Transform(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif