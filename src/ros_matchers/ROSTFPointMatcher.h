#ifndef rospoint
#define rospoint
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTFPointMatcher : public BaseMatcher {
public:
    ROSTFPointMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) {}
    virtual void search();
    virtual void run(const MatchFinder::MatchResult &Result);

};

#endif