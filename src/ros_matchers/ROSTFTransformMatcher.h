#ifndef rostrans
#define rostrans
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTFTransformMatcher : public BaseMatcher {
public:
    ROSTFTransformMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) {}
    virtual void search();
    virtual void run(const MatchFinder::MatchResult &Result);

};

#endif