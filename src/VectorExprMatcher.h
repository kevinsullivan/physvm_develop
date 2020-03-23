#include "BaseMatcher.h"


#ifndef vectorm
#define vectorm

class VectorExprMatcher : public BaseMatcher {
public:
    VectorExprMatcher(clang::ASTContext* context) : BaseMatcher(context) {}
    virtual void search();
    virtual void run(const MatchFinder::MatchResult &Result);

};

#endif