
#ifndef ROSTFStampedTransformguard
#define ROSTFStampedTransformguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTFStampedTransform : public BaseMatcher {
public:
    ROSTFStampedTransform(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif