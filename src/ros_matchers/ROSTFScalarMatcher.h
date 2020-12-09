
#ifndef ROSTFScalarMatcherguard
#define ROSTFScalarMatcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTFScalarMatcher : public BaseMatcher {
public:
    ROSTFScalarMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif