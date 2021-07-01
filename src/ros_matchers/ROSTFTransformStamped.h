
#ifndef ROSTFTransformStampedguard
#define ROSTFTransformStampedguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTFTransformStamped : public BaseMatcher {
public:
    ROSTFTransformStamped(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif