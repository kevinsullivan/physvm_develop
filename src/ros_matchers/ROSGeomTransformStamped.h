
#ifndef ROSGeomTransformStampedguard
#define ROSGeomTransformStampedguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSGeomTransformStamped : public BaseMatcher {
public:
    ROSGeomTransformStamped(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif