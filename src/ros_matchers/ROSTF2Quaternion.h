
#ifndef ROSTF2Quaternionguard
#define ROSTF2Quaternionguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTF2Quaternion : public BaseMatcher {
public:
    ROSTF2Quaternion(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif