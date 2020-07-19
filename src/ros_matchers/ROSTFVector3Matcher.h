#ifndef rosvec3
#define rosvec3
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTFVector3Matcher : public BaseMatcher {
public:
    ROSTFVector3Matcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) {}
    virtual void search();
    virtual void run(const MatchFinder::MatchResult &Result);

};

#endif