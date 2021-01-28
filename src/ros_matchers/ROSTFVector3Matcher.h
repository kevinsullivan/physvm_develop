
#ifndef ROSTFVector3Matcherguard
#define ROSTFVector3Matcherguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTFVector3Matcher : public BaseMatcher {
public:
    ROSTFVector3Matcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif