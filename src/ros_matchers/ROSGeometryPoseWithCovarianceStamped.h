
#ifndef ROSGeometryPoseWithCovarianceStampedguard
#define ROSGeometryPoseWithCovarianceStampedguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSGeometryPoseWithCovarianceStamped : public BaseMatcher {
public:
    ROSGeometryPoseWithCovarianceStamped(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif