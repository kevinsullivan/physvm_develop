
#ifndef ROSGeometryMsgsPointStampedMatcherguard
#define ROSGeometryMsgsPointStampedMatcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSGeometryMsgsPointStampedMatcher : public BaseMatcher {
public:
    ROSGeometryMsgsPointStampedMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif