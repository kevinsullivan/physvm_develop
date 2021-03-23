
#ifndef ROSTFStampedPointguard
#define ROSTFStampedPointguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTFStampedPoint : public BaseMatcher {
public:
    ROSTFStampedPoint(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif