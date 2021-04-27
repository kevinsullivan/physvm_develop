
#ifndef ROSGeometryMsgsVector3StampedMatcherguard
#define ROSGeometryMsgsVector3StampedMatcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSGeometryMsgsVector3StampedMatcher : public BaseMatcher {
public:
    ROSGeometryMsgsVector3StampedMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif