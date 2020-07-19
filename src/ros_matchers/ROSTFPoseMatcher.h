#ifndef rospose
#define rospose
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTFPoseMatcher : public BaseMatcher {
public:
    ROSTFPoseMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) {}
    virtual void search();
    virtual void run(const MatchFinder::MatchResult &Result);

};

#endif