#ifndef rosscalar
#define rosscalar
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTFScalarMatcher : public BaseMatcher {
public:
    ROSTFScalarMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) {}
    virtual void search();
    virtual void run(const MatchFinder::MatchResult &Result);

};

#endif