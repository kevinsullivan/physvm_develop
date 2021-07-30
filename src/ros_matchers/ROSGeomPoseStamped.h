
#ifndef ROSGeomPoseStampedguard
#define ROSGeomPoseStampedguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSGeomPoseStamped : public BaseMatcher {
public:
    ROSGeomPoseStamped(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif