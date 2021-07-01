
#ifndef ROSTF2TransformStampedguard
#define ROSTF2TransformStampedguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTF2TransformStamped : public BaseMatcher {
public:
    ROSTF2TransformStamped(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif